# ------------------------------------------------------------------------------
# Script 3: Chapter Five
# Subject: ELL and CD Type Estimators
# Description: Two-level model with homoskedastic (HM) and Heteroskedastic (HT) level-one errors but HM level-two errors
# ------------------------------------------------------------------------------
rm(list=ls(all=TRUE))
# ------------------------------------------------------------------------------
# Loading Packages
# ------------------------------------------------------------------------------
library(Matrix)
library(mvtnorm)
library(FNN)
library(fANCOVA)
library(KernSmooth)
library(lokern)
library(kknn)
library(VGAM)
library(quantreg)
library(MASS)
library(abind)
library(foreach)
library(doMC) 
registerDoMC(20)
#-------------------------------------------------------------------------------
# Functions  
# ------------------------------------------------------------------------------
FGT.alpha<-function(y,z,alpha){ 
  # Function for FGT indicators # z: Poverty line
  # y: Income # alpha:0,1,2
  
  if (length(z)==1){
    t.z=ifelse(y<z,1,0)
    t.z.alpha=t.z*((rep(1,length(y))-y/z)^alpha)
    povert=sum(t.z.alpha)/length(y)
  }
  
  if (length(z)>1){
    
    povert<-rep(0,length(z))
    for (i in 1:length(z)){
      t.z=ifelse(y<z[i],1,0)
      t.z.alpha=t.z*((rep(1,length(y))-y/z[i])^alpha)
      povert[i]=sum(t.z.alpha)/length(y)}
  }
  povert
}
# ------------------------------------------------------------------------------
Var.Com.MM.2<-function(level.2,level.1,res.2,res.1){
  # HM at both levels # level.2: ID number of level 2 # level.1: ID number of level 1
  # res.2: Cluster level residuals (average of marginal residuals of respective cluster)
  # res.1: HH level residuals (Marginal residuals of HHs / OLS residuals)
  
  n.2<-as.vector(table(level.2))
  C<-length(n.2)
  ID.C<-unique(level.2)
  n.1<-length(level.1)
  n0.bar.2<-sum(n.2^2)/sum(n.2)
  s1.e<-sum((res.1-mean(res.1))^2)/(n.1-1)
  s2.e<-sum(n.2*(res.2-mean(res.1))^2)/(C-1)
  sigma2.2<-max(((n.1-1)*(C-1))/((n.1-n0.bar.2)*(n.1-C))*(-s1.e+s2.e),0)
  sigma2.1<-max((n.1-1)/(n.1-C)*s1.e-(C-1)/(n.1-C)*s2.e,0)
  list(sigma2.1=sigma2.1,sigma2.2=sigma2.2)
}
# ------------------------------------------------------------------------------
Var.Com.MM.2.H<-function(level.2,level.1,res.2,con.res.1){
  # HT at 1st level & HM at 2nd level
  # con.res.1: HH level conditional residuals 
  # con.res.1: (Marginal residuals of HHs - Cluster level residuals)
  
  n.2<-as.vector(table(level.2))
  n.1<-length(level.1)
  C<-length(n.2)
  ID.C<-unique(level.2)
  wc<-n.2/sum(n.2)
  tau.2.c<-tapply(con.res.1,level.2,var)/n.2
  sigma2.2<-max((sum(wc*(res.2-mean(res.2))^2)-sum(wc*(1-wc)*tau.2.c))/sum(wc*(1-wc)),0)
  list(sigma2.2=sigma2.2)
}
# ------------------------------------------------------------------------------
GLS.EST<-function(n.c,sigma2.ch,sigma2.c,x.matrix,y.s){
  # n.c is size of clusters
  # sigma2.ch is a vector (or constant) of variance components at HH level
  # sigma2.c is variance components at cluster level
  # Output: beta estimates with thier variance covariance matrix
  
  n<-sum(n.c)
  number.cluster.s<-length(n.c)
  
  if (length(sigma2.ch)==1){
    # Homoskedasticity at both levels
    sampleList <- list()
    for (i in 1:number.cluster.s) sampleList[[i]]<-diag(rep(sigma2.ch,n.c[i]))+sigma2.c*matrix(1,n.c[i],n.c[i])  
  }
  
  if (length(sigma2.ch)>1){
    # HT at 1st level & HM at 2nd level
    sampleList <- list()
    j<-1
    for (i in 1:number.cluster.s) {
      sampleList[[i]]<-diag(sigma2.ch[j:(j+n.c[i]-1)])+sigma2.c*matrix(1,n.c[i],n.c[i])   
      j<-j+n.c[i]
    }
  }
  
  V<-bdiag(sampleList)
  inv.V<-solve(V,sparse=TRUE)
  xtx<-(t(x.matrix)%*%inv.V%*%(x.matrix))
  xty<-(t(x.matrix)%*%inv.V%*%(y.s))
  beta.gls <- solve(xtx)%*%xty
  vcov.beta.gls<- solve(t(x.matrix)%*%(x.matrix)) %*% (t(x.matrix)%*%V%*%(x.matrix)) %*% solve(t(x.matrix)%*%(x.matrix))
  list(beta.gls=as.matrix(beta.gls),vcov.beta.gls=as.matrix(vcov.beta.gls)) 
}
# ------------------------------------------------------------------------------
sigma2.ch.ELL<-function(y,x.s,x.U){
  # HT modelling in ELL Method
  # x.s,x.U are the explanatory variables for HT
  
  A <- 1.05*max(y^2)
  h <- log(y^2/(A-y^2))
  reg.alpha <- lm(h~x.s)
  sigma2.alpha <- sum(reg.alpha$residuals^2)/reg.alpha$df.residual
  B <- exp(reg.alpha$fitted.values)
  sig2.ch.s <- A*B/(1+B) + 0.5*sigma2.alpha*(A*B)*(1-B)/((1+B)^3)
  alpha<-coef(reg.alpha)
  vcov.alpha<-vcov(reg.alpha)
  if (is.vector(x.U)) B.U <- exp(cbind(rep(1,length(x.U)),x.U)%*%alpha)
  if (is.matrix(x.U)) B.U <- exp(cbind(rep(1,dim(x.U)[1]),x.U)%*%alpha)
  sigma2.ch.U <- A*B.U/(1+B.U) + 0.5*sigma2.alpha*(A*B.U)*(1-B.U)/((1+B.U)^3)
  list(x.s=x.s,x.U=x.U,sigma2.ch.s=sig2.ch.s,sigma2.ch.U=sigma2.ch.U,alpha=alpha,vcov.alpha=vcov.alpha,A=A,sigma2.alpha=sigma2.alpha)
}
# ------------------------------------------------------------------------------
RES.VAR.STRATA.IGLS <- function(y.s,x.s,ID.C.s,ID.H.s,x.U,ID.C.U,ID.H.U,
                                quantiles,Iteration.no,tol=1e-50){
  # Residual variance estimation using stratification method based on IGLS method
  # For estimating heterskedastic residual variances based on stratification method
  # y,x,ID.C,ID.H for sample data set
  # x.s , x.U vector or Matrix 
  # data set should be ordered by cluster and HH
  # quantiles : How many groups are aimed and vector of percentiles (say: c(0:10)/max(c(0:10))
  # Iteration.no: How many maximum iteration is Fixed
  # return: No. of iteration, HT residual variances for both sample and population individuals,
  # return: homoskedastic 2nd var comp., IGLS.beta, var.cov(IGLS.beta) 
  
  group<-quantiles/max(quantiles)
  n<-length(y.s)
  if (is.vector(x.s)) {
    data.s<-data.frame(y=y.s,x=x.s,ID.C=ID.C.s,ID.H=ID.H.s)
    lm.model<-lm(y~x,data=data.s)
  }
  if (is.matrix(x.s)) {
    data.s<-data.frame(y=y.s,ID.C=ID.C.s,ID.H=ID.H.s)
    lm.model<-lm(y.s~ x.s)
  }
  data.s$u.ch<-resid(lm.model)
  eta.s<-as.vector(tapply(data.s$u.ch,data.s$ID.C,mean))
  n.c<-as.vector(table(data.s$ID.C))
  data.s$eps.s<-data.s$u.ch-rep(eta.s,n.c)
  data.s$y.hat<-fitted.values(lm.model)
  # 2nd var com assumimg Homoskedasticity at individual level
  sig2.HM<-Var.Com.MM.2(data.s$ID.C,data.s$ID.H,eta.s,data.s$u.ch)  
  # 2nd var com assumimg Heteroskedasticity at individual level 
  sig2.HT<-Var.Com.MM.2.H(data.s$ID.C,data.s$ID.H,eta.s,data.s$eps.s) 
  # Creating groups on the basis of gropus quantiles
  data.s<-within(data.s, decile <- as.integer(cut(y.hat, quantile(y.hat, probs=group), include.lowest=TRUE, labels=FALSE)))
  # Finding group means (varaince for that group) for the constructed groups
  data.s<-within(data.s, sig2.ch.hat <- ave(eps.s^2, decile, FUN = mean))
  if (is.vector(x.s)) X.ols<-cbind(rep(1,n),data.s$x)
  if (is.matrix(x.s)) X.ols<-cbind(rep(1,n), x.s)  
  # These estimates will change over iteration
  x0<-data.s$sig2.ch.hat  # Initial Residual variances
  sigma2.2<-sig2.HT$sigma2.2  # Initial 2nd variance component
  # Iterative GLS start from here
  i <- 1
  while (i <= Iteration.no) {
    gls.estimate.i<-GLS.EST(n.c,x0,sigma2.2,X.ols,data.s$y)
    data.s$y.hat.i<-X.ols%*%gls.estimate.i$beta.gls
    data.s$u.ch.i<-data.s$y-data.s$y.hat.i
    eta.i<-as.vector(tapply(data.s$u.ch.i,data.s$ID.C,mean))
    data.s$eps.i<-data.s$u.ch.i-rep(eta.i,n.c)
    data.s<-within(data.s, decile <- as.integer(cut(y.hat.i, quantile(y.hat.i, probs=group), include.lowest=TRUE, labels=FALSE)))
    # This decile will replace the initial decile estimates
    data.s<-within(data.s, sig2.ch.hat.i <- ave(eps.i^2, decile, FUN = mean))
    x1<-data.s$sig2.ch.hat.i # Iterated residual variances
    # Iterated 2nd variance component
    sigma2.2<-Var.Com.MM.2.H(data.s$ID.C,data.s$ID.H,eta.i,data.s$eps.i)$sigma2.2 
    i <- i + 1
    if (mean(abs(x1 - x0)^2) < tol) break
    x0 <- x1
  }
  # Ultimate residual variance estimates for the sample observation which will be used as population residual variance
  data.s$sig2.ch.hat<-x0
  sig2.ch.hat.s<-data.s$sig2.ch.hat
  # Ultimate quantiles for the sample observation which will be used as population quantiles
  y.decile<-as.vector(quantile(data.s$y.hat.i, probs=group))
  # Ultimate residual variances for each quantile which will be used in for population quantiles
  sig2.ch.decile<-as.vector(tapply(data.s$sig2.ch.hat,data.s$decile,mean))
  # Ultimate IGLS beat and their var.cov matrix   
  beta.igls=gls.estimate.i$beta.gls
  vcov.beta.igls=gls.estimate.i$vcov.beta.gls
  # Ultimate 2nd variance component using IGLS method 
  sigma2.2.HT.IGLS<-sigma2.2
  # Estimation of Residual variances for population individuals
  N<-ifelse (is.vector(x.U), length(x.U), dim(x.U)[1])
  X.U<-cbind(rep(1,N),x.U)
  data.U<-data.frame(ID.C=ID.C.U,ID.H=ID.H.U)
  data.U$y.fixed<-X.U%*%beta.igls
  cut.U<-y.decile
  # Capturing the minimum and maximum predicted values which are out of the estimated cut.off points
  cut.U[1]<-min(data.U$y.fixed)
  cut.U[length(cut.U)]<-max(data.U$y.fixed)
  # now creating the groups on the basis of cut.off points
  data.U<-within(data.U, decile <- as.integer(cut(y.fixed, cut.U,include.lowest=TRUE))) 
  data.U<-data.U[order(data.U$decile),]
  data.U<-within(data.U, sig2.ch.hat <- rep(sig2.ch.decile,as.vector(table(data.U$decile))))
  data.U<-data.U[order(data.U$ID.C,data.U$ID.H),]
  sig2.ch.hat.U<-data.U$sig2.ch.hat
  list(iteration=i,beta.igls=beta.igls,vcov.beta.igls=vcov.beta.igls,
       sig2.ch.hat.s=sig2.ch.hat.s,sig2.ch.hat.U=sig2.ch.hat.U,sigma2.2.HT.IGLS=sigma2.2.HT.IGLS)
} 
# ------------------------------------------------------------------------------
# Combined Function for Mean, DF, FGT : ELL Methods
# ------------------------------------------------------------------------------
ELL.PB.HM<- function(beta,var.beta,var.com.1,var.com.2,ID.D,ID.C,X.U,t,
                     parameter=c("MEAN","DF","FGT")){
  # Standard.ELL.HM : For estimating Distribution Functions (DFs)
  # Basic ELL Parametric method considering Homoskedastic Variance components
  # t is a value or a vector indicating poverty line
  
  N<-length(ID.D)
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
  eta.l<-rnorm(C,0,sqrt(var.com.2))
  eps.l<-rnorm(N,0,sqrt(var.com.1))
  y.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
  
  if (parameter=="MEAN"){
    y.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    F11<-tapply(y.l,ID.D,mean)
  }
  
  if (parameter=="DF"){
    y.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    
    if (length(t)==1) F11<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))
    
    if (length(t)>1){
      F11<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))),
                        nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
    }
    
  }
  
  if (parameter=="FGT"){
    y.l<-exp(cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l) # y.l is in original scale
    
    if (length(t)==1){
      F00<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))
      F11<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,1))
      F22<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,2))
    }
    
    if (length(t)>1){
      F00<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
      F11<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,1))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
      F22<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,2))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
    }
    
  }
  
#  if (parameter=="MEAN") {list(F11=F11)}
#  if (parameter=="DF") list(F11=F11)
#  if (parameter=="FGT") list(F00=F00,F11=F11,F22=F22)
  
#  ifelse (parameter=="MEAN", list(F11=F11), ifelse (parameter=="DF", list(F11=F11), list(F00=F00,F11=F11,F22=F22)))
  
#  ifelse (parameter=="FGT", list(F00=F00,F11=F11,F22=F22), list(F11=F11))
  if (parameter=="FGT") list(F00=F00,F11=F11,F22=F22) else list(F11=F11)
  
}
# ------------------------------------------------------------------------------
ELL.PB.HT<- function(beta,var.beta,alpha,var.alpha,sigma2.alpha,var.com.cluster,
                     ID.D,ID.C,X.U,A,t,parameter=c("MEAN","DF","FGT")){
  # Estimating Distribution function: PB procedure
  # HT at level-One
  
  N<-length(ID.D)
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
  alpha.l<-mvtnorm::rmvnorm(1,alpha,var.alpha)
  B <- exp(cbind(rep(1,N),X.U)%*%t(alpha.l))
  var.com.HH.U <- A*B/(1+B) + 0.5*sigma2.alpha*(A*B)*(1-B)/((1+B)^3)
  eta.l<-rnorm(C,0,sqrt(var.com.cluster))
  eps.l<-rnorm(N,0,sqrt(var.com.HH.U))
  
  if (parameter=="MEAN"){
    y.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    F11<-tapply(y.l,ID.D,mean)
  #  list(F11=F11)
  }
  
  if (parameter=="DF"){
    y.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    if (length(t)==1) F11<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))
    if (length(t)>1){
      F11<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
    }
  #  list(F11=F11)
  }
  
  if (parameter=="FGT"){
    y.l<-exp(cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l)
    if (length(t)==1){
      F00<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))
      F11<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,1))
      F22<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,2))
    }
    if (length(t)>1){
      F00<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
      F11<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,1))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
      F22<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,2))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
    }
  #  list(F00=F00,F11=F11,F22=F22)
  }
  if (parameter=="FGT") list(F00=F00,F11=F11,F22=F22) else list(F11=F11)
  
}
# ------------------------------------------------------------------------------
ELL.NPB.HM<- function(beta,var.beta,eta.s,eps.s,var.com.1,var.com.2,ID.C.s,ID.D,
  ID.C,X.U,t,parameter=c("MEAN","DF","FGT"),
  residual.1=c("unconditional","conditional")){
  # Estimating Distribution function
  # Basic ELL Non-Parametric Bootstrap (NPB) procedure considering HM errors
  
  N<-length(ID.D)
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  eta.u.scl<-eta.s*scale.2
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  eps.s.scl<-eps.s*scale.1
  if (residual.1=="unconditional") {
    eta.l<-sample(eta.u.scl,C,replace=TRUE)
    eps.l<-sample(eps.s.scl,N,replace=TRUE)
  }
  if (residual.1=="conditional") {
    ID.C.sampling<-sample(c(1:length(unique(ID.C.s))),C,replace=TRUE)
    eta.l<-eta.u.scl[ID.C.sampling]
    ID.C.sampled<-unique(ID.C.s)[ID.C.sampling]
    eps.l<-NULL
    for (c in 1:C){
      eps.U<-sample(eps.s.scl[ID.C.s==ID.C.sampled[c]],N.c[c],replace=TRUE)
      eps.l<-c(eps.l,eps.U)
    }
  }
  if (parameter=="MEAN"){
    y.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    F11<-tapply(y.l,ID.D,mean)
   # list(F11=F11)
  }
    
  if (parameter=="DF"){
    y.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    if (length(t)==1){
      F11<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))
    }
    if (length(t)>1){
      F11<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
    }
   # list(F11=F11)
  }
  if (parameter=="FGT"){
    y.l<-exp(cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l)
    if (length(t)==1){
      F00<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))
      F11<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,1))
      F22<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,2))
    }
    if (length(t)>1){
      F00<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
      F11<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,1))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
      F22<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,2))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
    }
    #list(F00=F00,F11=F11,F22=F22)
  }
  
  if (parameter=="FGT") list(F00=F00,F11=F11,F22=F22) else list(F11=F11)
  
}
# ------------------------------------------------------------------------------
ELL.NPB.HT<- function(beta,var.beta,alpha,var.alpha,sigma2.alpha,eta.s,eps.s,
  sig2.eps.s,ID.C.s,ID.D,ID.C,X.U,A,t,parameter=c("MEAN","DF","FGT"),
  residual.1=c("unconditional","conditional")){
  # Semi-parametric Bootstrap (SPB) procedure (ELL, 2002,2003)
  # Estimating Distribution function
  # Heteroskedastic error variances based on logistic function 
  # t is here a value but need to be a vector
  # Conditional: Draw individual level effects for a population cluster from - 
  # sample cluster whose random effect is randomly drawn for the population cluster 
  # Unconditional: Draw without restriction of drawing cluster random effects 
  # eta.s should be ordered in ID.C.s
  # eps.s and sig2.eps.s should be ordered in ID.C.s
  # Sample and population data sets should be ordered by area and clusters
  
  N<-length(ID.D)
  N.d<-as.vector(table(ID.D))
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
  alpha.l<-mvtnorm::rmvnorm(1,alpha,var.alpha)
  B <- exp(cbind(rep(1,N),X.U)%*%t(alpha.l))
  var.com.HH.U <- A*B/(1+B) + 0.5*sigma2.alpha*(A*B)*(1-B)/((1+B)^3)
  # standardized the residuals using the individual specific residuals
  eps.std<-eps.s/sqrt(sig2.eps.s)-mean(eps.s/sqrt(sig2.eps.s))
  if (residual.1=="unconditional") {
    eta.l<-sample(eta.s,C,replace=TRUE)
    eps.l<-sample(eps.std,N,replace=TRUE)*sqrt(var.com.HH.U)
  }
  if (residual.1=="conditional") {
    ID.C.sampling<-sample(c(1:length(unique(ID.C.s))),C,replace=TRUE)
    eta.l<-eta.s[ID.C.sampling]
    ID.C.sampled<-unique(ID.C.s)[ID.C.sampling]
    eps.u.std<-NULL
    for (c in 1:C){
      eps.U<-sample(eps.std[ID.C.s==ID.C.sampled[c]],N.c[c],replace=TRUE)
      eps.u.std<-c(eps.u.std,eps.U)
    }
    eps.l<-eps.u.std*sqrt(var.com.HH.U)
  }
  if (parameter=="MEAN"){
    y.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    F11<-tapply(y.l,ID.D,mean)
   # list(F11=F11)
  }
  if (parameter=="DF"){
    y.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    if (length(t)==1){
      F11<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))
    }
    if (length(t)>1){
      F11<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
    }
  #  list(F11=F11)
  }
  
  if (parameter=="FGT"){
    y.l<-exp(cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l) # y.l is in original scale
    if (length(t)==1){
      F00<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))
      F11<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,1))
      F22<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,2))
    }
    if (length(t)>1){
      F00<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
      F11<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,1))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
      F22<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,2))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
    }
  #  list(F00=F00,F11=F11,F22=F22)
  }
  
  if (parameter=="FGT") list(F00=F00,F11=F11,F22=F22) else list(F11=F11)
  
}
# ------------------------------------------------------------------------------
# Combined Function for Mean, DF, FGT : CDSM Methods
# ------------------------------------------------------------------------------
CD.SM.HM<-function(beta,var.beta,eta.s,eps.s,var.com.1,var.com.2,ID.D,ID.C,
  X.U,t,parameter=c("MEAN","DF","FGT"),residual.1=c("Fixed","Random")){
  # CD estimator for Homogeneous variance component at two levels 
  # var.com.1 and var.com.1.U are scalar
  # Scale residuals if methodology is based on scaled residuals
  # Use raw residuals if methodology is based on unscaled residuals
  
  n<-length(eps.s)
  N<-length(ID.D)
  C<-length(unique(ID.C))
  N.c<-as.vector(table(ID.C))
  beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
  eta.u<-sample(eta.s,C,replace=TRUE)
  std.eps.s<-eps.s/sqrt(var.com.1)
  if (residual.1=="Fixed") eps.l<-std.eps.s
  if (residual.1=="Random") eps.l<-sample(std.eps.s,n,replace=TRUE)
  eps.u.l <- outer(sqrt(rep(var.com.1,N)),eps.l)
  
  if (parameter=="MEAN"){
    y.l<-as.vector(cbind(rep(1,N),X.U)%*%t(beta.l))+rep(eta.u,N.c)+eps.u.l
    F.t<-rowSums(y.l)/dim(y.l)[2]
    F11<-tapply(F.t,ID.D,mean)
   # list(F11=F11)
  }
  if (parameter=="DF"){
    y.l<-as.vector(cbind(rep(1,N),X.U)%*%t(beta.l))+rep(eta.u,N.c)+eps.u.l
    if (length(t)==1){
      AA<-y.l<t
      F.t<-rowSums(AA)/dim(AA)[2]
      F11<-tapply(F.t,ID.D,mean)
    }
    if (length(t)>1){
      F11<-array(0,dim=c(1,length(unique(ID.D)),length(t)))
      for (i in 1:length(t)){
        AA<-y.l<t[i]
        F.t<-rowMeans(AA)
        F11[,,i]<-tapply(F.t,ID.D,mean)
      }
    }
  #  list(F11=F11)
  }
    
  if (parameter=="FGT"){
    y.l<-exp(as.vector(cbind(rep(1,N),X.U)%*%t(beta.l))+rep(eta.u,N.c)+eps.u.l) # y.l is in original scale
    
    if (length(t)==1){
      AA<-y.l<t
      F0.t<-rowMeans(AA)
      
      B<-y.l
      B[which(B<0)]<-0
      BB<-((t-B)/t)*AA 
      F1.t<-rowMeans(BB)
      
      CC<-((t-B)/t)^2*AA 
      F2.t<-rowMeans(CC)
      
      F00<-tapply(F0.t,ID.D,mean)
      F11<-tapply(F1.t,ID.D,mean)
      F22<-tapply(F2.t,ID.D,mean)
      
    }
    
    if (length(t)>1){
      
      F00<-array(0,dim=c(1,length(unique(ID.D)),length(t)))
      F11<-array(0,dim=c(1,length(unique(ID.D)),length(t)))
      F22<-array(0,dim=c(1,length(unique(ID.D)),length(t)))
      
      for (i in 1:length(t)){
        AA<-y.l<t[i]
        F0.t<-rowMeans(AA)
        F00[,,i]<-tapply(F0.t,ID.D,mean)
        
        B<-y.l
        B[which(B<0)]<-0
        BB<-((t[i]-B)/t[i])*AA 
        F1.t<-rowMeans(BB)
        F11[,,i]<-tapply(F1.t,ID.D,mean)
        
        CC<-((t[i]-B)/t[i])^2*AA 
        F2.t<-rowMeans(CC)
        F22[,,i]<-tapply(F2.t,ID.D,mean)
      }
    }
    
   # list(F00=F00,F11=F11,F22=F22)
    
  }
  if (parameter=="FGT") list(F00=F00,F11=F11,F22=F22) else list(F11=F11)
  
}
# ------------------------------------------------------------------------------
CD.SM.HT<-function(beta,var.beta,eta.s,eps.s,var.com.2,var.com.1,var.com.HH.s,var.com.HH.U,
  ID.D,ID.C,X.U,t,parameter=c("MEAN","DF","FGT"),residual.1=c("Fixed","Random")){
  # CD estimator for Homogeneous variance component at 2nd level but heterogeneous variance component at 1st level
  # Scale the residuals before utilize them in BP as -
  # scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1))) 
  # scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1))) 
  # eta.s.scl<-eta.s*scale.2  
  # eps.s.scl<-eps.s*scale.1
  
  n<-length(eps.s) 
  N<-length(ID.D)
  C<-length(unique(ID.C))
  N.c<-as.vector(table(ID.C))
  beta.l<-mvtnorm::rmvnorm(1,beta,var.beta) 
  eta.u<-sample(eta.s,C,replace=TRUE)
  std.eps.s<-eps.s/sqrt(var.com.HH.s) ; 
  if (residual.1=="Fixed") eps.l<-std.eps.s
  if (residual.1=="Random") eps.l<-sample(std.eps.s,n,replace=TRUE)

  if (parameter=="MEAN"){
    y.l<-as.vector(cbind(rep(1,N),X.U)%*%t(beta.l))+rep(eta.u,N.c)+outer(sqrt(var.com.HH.U),eps.l)
    F.t<-rowSums(y.l)/dim(y.l)[2]
    F11<-tapply(F.t,ID.D,mean)
  #  list(F11=F11)
  }

  if (parameter=="DF"){
    y.l<-as.vector(cbind(rep(1,N),X.U)%*%t(beta.l))+rep(eta.u,N.c)+outer(sqrt(var.com.HH.U),eps.l)
    if (length(t)==1){
      AA<-y.l<t ; F.t<-rowSums(AA)/dim(AA)[2] ; F11<-tapply(F.t,ID.D,mean)
      AA <- NULL
    }
    
    if (length(t)>1){ 
      F11<-array(0,dim=c(1,length(unique(ID.D)),length(t))) ; 
      
      for (i in 1:length(t)){
        AA<-y.l<t[i] ; F.t<-rowMeans(AA) ; F11[,,i]<-tapply(F.t,ID.D,mean)
        AA <- NULL
      }
    }
  #  list(F11=F11)
  }

  if (parameter=="FGT"){
    y.l<-exp(as.vector(cbind(rep(1,N),X.U)%*%t(beta.l))+rep(eta.u,N.c)+outer(sqrt(var.com.HH.U),eps.l))
      if (length(t)==1){
      AA<-y.l<t
      F0.t<-rowMeans(AA)
      B<-y.l
      B[which(B<0)]<-0
      BB<-((t-B)/t)*AA 
      F1.t<-rowMeans(BB)
      CC<-((t-B)/t)^2*AA 
      F2.t<-rowMeans(CC)
      F00<-tapply(F0.t,ID.D,mean)
      F11<-tapply(F1.t,ID.D,mean)
      F22<-tapply(F2.t,ID.D,mean)
      AA <- NULL
      B  <- NULL
      BB <- NULL
      CC <- NULL
    }
    if (length(t)>1){
      F00<-array(0,dim=c(1,length(unique(ID.D)),length(t)))
      F11<-array(0,dim=c(1,length(unique(ID.D)),length(t)))
      F22<-array(0,dim=c(1,length(unique(ID.D)),length(t)))
      for (i in 1:length(t)){
        AA<-y.l<t[i]
        F0.t<-rowMeans(AA)
        F00[,,i]<-tapply(F0.t,ID.D,mean)
        B<-y.l
        B[which(B<0)]<-0
        BB<-((t[i]-B)/t[i])*AA 
        F1.t<-rowMeans(BB)
        F11[,,i]<-tapply(F1.t,ID.D,mean)
        CC<-((t[i]-B)/t[i])^2*AA 
        F2.t<-rowMeans(CC)
        F22[,,i]<-tapply(F2.t,ID.D,mean)
        AA <- NULL
        B  <- NULL
        BB <- NULL
        CC <- NULL
      }
    }
  #  list(F00=F00,F11=F11,F22=F22)
  }    
  if (parameter=="FGT") list(F00=F00,F11=F11,F22=F22) else list(F11=F11)
}
# ------------------------------------------------------------------------------
# Combined Function for Mean, DF, FGT : CDMC Methods
# ------------------------------------------------------------------------------
CD.MC.HM<-function(beta,var.beta,eta.s,eps.s,var.com.1,var.com.2,ID.D,ID.C,X.U,t,parameter=c("MEAN","DF","FGT")){
  # Following the Marchetti et al (2012) as an alternative of CD approach
  
  N<-length(ID.D)
  C<-length(unique(ID.C))
  N.c<-as.vector(table(ID.C))
  beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
  eta.u<-sample(eta.s,C,replace=TRUE)
  std.eps.s<-eps.s/sqrt(var.com.1) # -mean(eps.s/sqrt(var.com.1))
  eps.u.l<-sample(std.eps.s,N,replace=TRUE)
  eps.l<-sqrt(var.com.1)*eps.u.l

  if (parameter=="MEAN"){
    y.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.u,N.c)+eps.l
    F11<-tapply(y.l,ID.D,mean)
  #  list(F11=F11)
  }

  if (parameter=="DF"){
    y.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.u,N.c)+eps.l
    if (length(t)==1) F11<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))
    
    if (length(t)>1){
      F11<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
    }
  #  list(F11=F11)
  }
  if (parameter=="FGT"){
    y.l<-exp(cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.u,N.c)+eps.l) # y.l is in original scale
    if (length(t)==1){
      F00<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))
      F11<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,1))
      F22<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,2))
    }
    if (length(t)>1){
      F00<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
      F11<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,1))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
      F22<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,2))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
    }
  #  list(F00=F00,F11=F11,F22=F22)  
  }
  if (parameter=="FGT") list(F00=F00,F11=F11,F22=F22) else list(F11=F11)
}
# ------------------------------------------------------------------------------
CD.MC.HT<-function(beta,var.beta,eta.s,eps.s,var.com.2,var.com.1,var.com.HH.s,
            var.com.HH.U,ID.D,ID.C,X.U,t,parameter=c("MEAN","DF","FGT")){
  # Following the Marchetti et al (2012) as an alternative of CD approach
  # Scale the residuals before utilize them in BP as -
  # scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  # scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  # eta.s.scl<-eta.s*scale.2
  # eps.s.scl<-eps.s*scale.1
  
  N<-length(ID.D)
  C<-length(unique(ID.C))
  N.c<-as.vector(table(ID.C))
  beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
  eta.u<-sample(eta.s,C,replace=TRUE)  
  std.eps.s<-eps.s/sqrt(var.com.HH.s)#-mean(eps.s.scl/sqrt(var.com.HH.s))
  eps.u.l<-sample(std.eps.s,N,replace=TRUE)
  eps.l<-sqrt(var.com.HH.U)*eps.u.l
  
  if (parameter=="MEAN"){
    y.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.u,N.c)+eps.l
    F11<-tapply(y.l,ID.D,mean)
  #  list(F11=F11)
  }
  
  if (parameter=="DF"){
    y.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.u,N.c)+eps.l
    if (length(t)==1) F11<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))
    if (length(t)>1){
      F11<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
    }
  #  list(F11=F11)
  }
  
  if (parameter=="FGT"){
    y.l<-exp(cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.u,N.c)+eps.l) # y.l is in original scale
    if (length(t)==1){
      F00<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))
      F11<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,1))
      F22<-tapply(y.l,ID.D,function (x) FGT.alpha(x,t,2))
    }
    if (length(t)>1){
      F00<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,0))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
      F11<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,1))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
      F22<-array(matrix(simplify2array(tapply(y.l,ID.D,function (x) FGT.alpha(x,t,2))),nrow=length(unique(ID.D)),ncol=length(t),byrow=TRUE),
                 dim=c(1,length(unique(ID.D)),length(t)))
    }
   # list(F00=F00,F11=F11,F22=F22)
  }
  if (parameter=="FGT") list(F00=F00,F11=F11,F22=F22) else list(F11=F11)
}
# ------------------------------------------------------------------------------
# Function for Simulation Study: Type-I - Mean & DF : ELL Methods
# ------------------------------------------------------------------------------
Simulation.ELL.SADF<-function(N.Area,N.Cluster,C.d.s,N.c.s,df,sig2.eta,Prob.C,
  het.func=c("f1","f2","f3","f4","f4b"),skedasticity=c("Homoskedastic","Heteroskedastic"),
  Bootstrap=c("PB","NPB"),residual.1=c("unconditional","conditional"),quant,
  parameter=c("MEAN","DF"),No.Boot,No.Sim){

  # Population structure
  D<-length(N.Area)
  No.Area<-D
  C<-length(N.Cluster)
  N<-sum(N.Cluster)
  N.d<-N.Area
  N.c<-N.Cluster
  
  ID.D<-rep(1:D,N.d)
  ID.C<-rep(1:C,N.c)
  ID.H<-c(1:N)
  
  # Sample structure
  # C.d.s   # Number of cluster per small area in  sample
  # N.c.s   # Number of individuals per small cluster in  sample 
  
  n<-sum(N.c.s)
  
  trials<-No.Sim
  Sigma.HM<-matrix(0,trials,2)
  Sigma.HT<-matrix(0,trials,2)
  
  # Individual-specific variance components : Sample
  
  sigma2.ch.s<-matrix(0,n,trials)     # True 
  sigma2.ch.s.1<-matrix(0,n,trials) # Using ELL logistic method
  
  # Individual-specific variance components : Population
  
  sigma2.ch.U<-matrix(0,N,trials)     # True 
  sigma2.ch.U.1<-matrix(0,N,trials) # Using ELL logistic method
  

  No.Q=ifelse(parameter=="MEAN",1,length(quant))
  
  if (No.Q==1) {
    
    F.True<-array(0,dim=c(trials,No.Area))  # True estimates: SADF 
    F11<-array(0,dim=c(trials,No.Area))     # ELL estimates: SADF
    F11.MSE<-array(0,dim=c(trials,No.Area)) # MSE of ELL estimates: SADF
    CR.I<-array(0,dim=c(trials,No.Area))     # Coverage Indicator of 95% CI  
    
  }
  
  
  if (No.Q>1) {
    
    F.True<-array(0,dim=c(trials,No.Area,No.Q))    # True estimates: FGT 0
    F11<-array(0,dim=c(trials,No.Area,No.Q))       # ELL estimates FGT 0: PB
    F11.MSE<-array(0,dim=c(trials,No.Area,No.Q))   # ELL estimates FGT 0: PB
    CR.I<-array(0,dim=c(trials,No.Area,No.Q))       # Coverage Indicator of 95% CI
    
  }
  
  # Parallel Object Creation
  
  # The foreach command is used for the Bootstrap work (Inner loop)
  # f2 is for single quantile
  f2 <- function(obj1,obj2) {
    z <- list(
      F11.True=rbind(obj1$F11.True,obj2$F11.True)
    )
  }
  # f2.array is for multiple quantile
  f2.array <- function(obj1,obj2) {
    z <- list(
      F11.True=abind(obj1$F11.True,obj2$F11.True,along=1)
    )
  }
  
  # Simulation study strat from here 
  
  for (s in 1:trials){
    
    cat(date(),"Iteration number",s,"starting","\n",fill=T)
  
    # Generating explanatory variable
    
    x.ch<-rchisq(N,df)
    
    # Generating cluster-specific random errors 
    
    eta.c<-rnorm(C,0,sqrt(sig2.eta))
    
    # Generating individual-specific random errors 
    
    if (het.func=="f1") sig2.ch<-sig2.ch.1(x.ch)
    if (het.func=="f2") sig2.ch<-sig2.ch.2(x.ch)
    if (het.func=="f3") sig2.ch<-sig2.ch.3(x.ch)
    
    if (het.func=="f4") {
      z.ch<-rbinom(N,1,Prob.C)
      sig2.ch<-sig2.ch.4(x.ch,z.ch)
    }
    
    if (het.func=="f4b") {
      z.ch<-rbinom(N,1,Prob.C)
      sig2.ch<-sig2.ch.4(x.ch,z.ch)
    }
    
    eps.ch<-rnorm(N,0,sqrt(sig2.ch))
    
    # Generating response values for individuals 
    
    y.ch<-500+1.5*x.ch+rep(eta.c,N.c)+eps.ch
    
    data.1<-data.frame(ID.D=ID.D,ID.C=ID.C,ID.H=ID.H,x=x.ch,y=y.ch,sig2.ch=sig2.ch)
    
    if (parameter=="MEAN") t<-mean(data.1$y) else t<-as.vector(quantile(data.1$y,quant))
    
    # Draw the sample from the population
    
    EA.sample=NULL
    
    for (d in 1:D){
      if (length(C.d.s)==1) id.EA.sample=sort(sample(unique(ID.C[ID.D==d]),C.d.s)) # Randomly selection of 2 EAs from each small area & sorted
      if (length(C.d.s)>1) id.EA.sample=sort(sample(unique(ID.C[ID.D==d]),C.d.s[d])) # Randomly selection of 2 EAs from each small area & sorted
      EA.sample<-c(EA.sample,id.EA.sample)
    }
    
    ID.sample<-NULL
    
    for (a in 1:length(EA.sample)){
      if (length(N.c.s)==1) ID.s<-sort(sample(ID.H[ID.C==EA.sample[a]],N.c.s))
      if (length(N.c.s)>1)  ID.s<-sort(sample(ID.H[ID.C==EA.sample[a]],N.c.s[a]))
      
      if (length(N.c.s)==1 & het.func=="f4b")  ID.s<-sort(sample(ID.H[ID.C==EA.sample[a] & z.ch==0],N.c.s))
      if (length(N.c.s)>1 & het.func=="f4b")  ID.s<-sort(sample(ID.H[ID.C==EA.sample[a] & z.ch==0],N.c.s[a]))
      
      ID.sample<-c(ID.sample,ID.s)
    }
    
    
    data1.s<-data.1[ID.sample,]
    
    n<-length(data1.s$y)
    n.c<-tapply(data1.s$ID.H,data1.s$ID.C,length)
    number.cluster.s<-length(unique(data1.s$ID.C))
    ID.cluster.s<-unique(data1.s$ID.C)
    
    # Fit the OLS model
    
    lm1<-lm(y~x,data1.s)
    data1.s$uch.1<-resid(lm1)
    eta.1<-as.vector(tapply(data1.s$uch.1,data1.s$ID.C,mean))
    data1.s$eps.1<-data1.s$uch.1-rep(eta.1,n.c)
    data1.s$y.hat<-fitted.values(lm1)
    
    # Estimation of variance  component at level 2 assumong homo.. and hete.. at level one
    
    sig2.HM.1<-Var.Com.MM.2(data1.s$ID.C,data1.s$ID.H,eta.1,data1.s$uch.1)   # Homoskedasticity at individual level
    sig2.HT.1<-Var.Com.MM.2.H(data1.s$ID.C,data1.s$ID.H,eta.1,data1.s$eps.1) # Heteroskedasticity at individual level
    
    # Residual Variance estimates at level one
    
    # ELL estimates 
    
    Sigma2.ch.ELL<-sigma2.ch.ELL(data1.s$eps.1,data1.s$x,data.1$x)
    
    alpha.hat<-Sigma2.ch.ELL$alpha
    cov.alpha.hat<-Sigma2.ch.ELL$vcov.alpha
    A<-Sigma2.ch.ELL$A
    sigma2.alpha<-Sigma2.ch.ELL$sigma2.alpha
    
    # Estimated results for individuals: ELL
    data1.s$sig2.ch.hat.1<-Sigma2.ch.ELL$sigma2.ch.s
    data.1$sig2.ch.hat.1<-Sigma2.ch.ELL$sigma2.ch.U
    
    # Store the Variance components
    
    Sigma.HM[s,]<-c(sig2.HM.1$sigma2.2,sig2.HM.1$sigma2.1)
    Sigma.HT[s,]<-c(sig2.HT.1$sigma2.2,((summary(lm1)$sigma)^2-sig2.HT.1$sigma2.2))
    
    sigma2.ch.s[,s]<-data1.s$sig2.ch # True for sample observations
    sigma2.ch.s.1[,s]<-data1.s$sig2.ch.hat.1 # Using logistic method for sample observations
    
    sigma2.ch.U[,s]<-data.1$sig2.ch # True for Population observations
    sigma2.ch.U.1[,s]<-data.1$sig2.ch.hat.1 # Using logistic method for Population observations
    
    # Generalized least square estimates of the regression parameters
    
    X.ols<-cbind(rep(1,n),data1.s$x)
    
    
    # SADF using ELL PB method
    
    # Estimation using Parametric ELL Method with Homoskedastic variance components at both level

    if (skedasticity=="Homoskedastic" & Bootstrap=="PB"){
      
      gls.estimate<-GLS.EST(n.c,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      if (parameter=="MEAN"){
        F.True[s,]<-tapply(data.1$y,data.1$ID.D,mean)
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-ELL.PB.HM(beta.gls,var.beta.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("MEAN"))$F11
          list(F11.True=F11.True)
        }
        
        F11[s,]<-colMeans(r.FGT$F11.True)
        F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd) 
        F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
        F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
        CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        
      }
      
      if (parameter=="DF"){
        if (length(t)==1){
          F.True[s,]<-tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
            F11.True<-ELL.PB.HM(beta.gls,var.beta.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter="DF")$F11
            list(F11.True=F11.True)
          }
          
          F11[s,]<-colMeans(r.FGT$F11.True)
          F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd) 
          F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
          
        }
        
        if (length(t)>1){
          F.True[s,,]<-array(matrix(simplify2array(tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t)))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
            F11.True<-ELL.PB.HM(beta.gls,var.beta.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter="DF")$F11
            list(F11.True=F11.True)
          }
          
          F11[s,,]<-colMeans(r.FGT$F11.True,dims=1)
          
          
          #        F11.SE<-array(0,dim=c(dim(r.FGT$F11.True)[2],dim(r.FGT$F11.True)[3]))
          #        for (i in 1:dim(r.FGT$F11.True)[3]) F11.SE[,i]<-apply(r.FGT$F11.True[,,i],2,sd)
          #        F11.MSE[s,,]<-F11.SE    
          
          F11.MSE[s,,]<-apply(r.FGT$F11.True,c(2,3),sd)
          F11.Q.02.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,,]<-(F.True[s,,]>=F11.Q.02.5 & F.True[s,,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        } 
      }
      
    } # ELL.PB.HM End
    
    if (skedasticity=="Heteroskedastic" & Bootstrap=="PB"){
      
      # Heteroskedastic variance components: Using Logistic Function
      gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.1,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      if (parameter=="MEAN"){
        F.True[s,]<-tapply(data.1$y,data.1$ID.D,mean)
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-ELL.PB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,sig2.HT.1$sigma2.2,data.1$ID.D,data.1$ID.C,data.1$x,A,t,parameter="MEAN")$F11
          list(F11.True=F11.True)
        }
        
        F11[s,]<-colMeans(r.FGT$F11.True)
        F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd) 
        F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
        F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
        CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      }
      
      
      if (parameter=="DF"){
        
        if (length(t)==1){
          F.True[s,]<-tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
            F11.True<-ELL.PB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,sig2.HT.1$sigma2.2,data.1$ID.D,data.1$ID.C,data.1$x,A,t,parameter="DF")$F11
            list(F11.True=F11.True)
          }
          F11[s,]<-colMeans(r.FGT$F11.True)
          F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd) 
          F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
          
        }
        
        if (length(t)>1){
          F.True[s,,]<-array(matrix(simplify2array(tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t)))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
            F11.True<-ELL.PB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,sig2.HT.1$sigma2.2,data.1$ID.D,data.1$ID.C,data.1$x,A,t,parameter="DF")$F11
            list(F11.True=F11.True)
          }
          
          F11[s,,]<-colMeans(r.FGT$F11.True,dims=1)
          F11.MSE[s,,]<-apply(r.FGT$F11.True,c(2,3),sd)
          F11.Q.02.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,,]<-(F.True[s,,]>=F11.Q.02.5 & F.True[s,,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        }
      }
       
      
    } # ELL.PB.HT End
    
    if (skedasticity=="Homoskedastic" & Bootstrap=="NPB" & residual.1=="unconditional"){
      
      gls.estimate<-GLS.EST(n.c,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      if (parameter=="MEAN"){
        F.True[s,]<-tapply(data.1$y,data.1$ID.D,mean)
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-ELL.NPB.HM(beta.gls,var.beta.gls,eta.1,data1.s$eps.1,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data1.s$ID.C,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("MEAN"),residual.1=c("unconditional"))$F11
          list(F11.True=F11.True)
        }
        F11[s,]<-colMeans(r.FGT$F11.True)
        F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)  
        F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
        F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
        CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        
      }
      
      if (parameter=="DF"){
        
        if (length(t)==1){ 
          F.True[s,]<-tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))
          r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
            F11.True<-ELL.NPB.HM(beta.gls,var.beta.gls,eta.1,data1.s$eps.1,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data1.s$ID.C,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("DF"),residual.1=c("unconditional"))$F11
            list(F11.True=F11.True)
          }
          F11[s,]<-colMeans(r.FGT$F11.True)
          F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)  
          F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        }
        
        if (length(t)>1){
          F.True[s,,]<-array(matrix(simplify2array(tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t)))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
            F11.True<-ELL.NPB.HM(beta.gls,var.beta.gls,eta.1,data1.s$eps.1,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data1.s$ID.C,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("DF"),residual.1=c("unconditional"))$F11
            list(F11.True=F11.True)
          }
          F11[s,,]<-colMeans(r.FGT$F11.True,dims=1)
          F11.MSE[s,,]<-apply(r.FGT$F11.True,c(2,3),sd)
          F11.Q.02.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,,]<-(F.True[s,,]>=F11.Q.02.5 & F.True[s,,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
          
        } 
      }

      
    } # ELL.NPB.HM End
    
    if (skedasticity=="Homoskedastic" & Bootstrap=="NPB" & residual.1=="conditional"){
      
      gls.estimate<-GLS.EST(n.c,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      if (parameter=="MEAN"){
        F.True[s,]<-tapply(data.1$y,data.1$ID.D,mean)
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-ELL.NPB.HM(beta.gls,var.beta.gls,eta.1,data1.s$eps.1,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,
                               data1.s$ID.C,data.1$ID.D,data.1$ID.C,data.1$x,t,
                               parameter=c("MEAN"),residual.1=c("conditional"))$F11
          list(F11.True=F11.True)
        }
        F11[s,]<-colMeans(r.FGT$F11.True)
        F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)  
        F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
        F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
        CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        
      }
      
      if (parameter=="DF"){
        
        if (length(t)==1){    
          F.True[s,]<-tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
            F11.True<-ELL.NPB.HM(beta.gls,var.beta.gls,eta.1,data1.s$eps.1,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,
                  data1.s$ID.C,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("DF"),residual.1=c("conditional"))$F11
            list(F11.True=F11.True)
          }
          F11[s,]<-colMeans(r.FGT$F11.True)
          F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)  
          F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
          
        }
        
        if (length(t)>1){
          F.True[s,,]<-array(matrix(simplify2array(tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t)))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
            F11.True<-ELL.NPB.HM(beta.gls,var.beta.gls,eta.1,data1.s$eps.1,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,
              data1.s$ID.C,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("DF"),residual.1=c("conditional"))$F11
            list(F11.True=F11.True)
          } 
          F11[s,,]<-colMeans(r.FGT$F11.True,dims=1)
          F11.MSE[s,,]<-apply(r.FGT$F11.True,c(2,3),sd)
          F11.Q.02.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,,]<-(F.True[s,,]>=F11.Q.02.5 & F.True[s,,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
          
        } 
      }
       
    } # ELL.NPB.HM End
    
    if (skedasticity=="Heteroskedastic" & Bootstrap=="NPB" & residual.1=="unconditional"){
      
      # Heteroskedastic variance components: Using Logistic Function
      gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.1,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      if (parameter=="MEAN"){
        F.True[s,]<-tapply(data.1$y,data.1$ID.D,mean)
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-ELL.NPB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,eta.1,data1.s$eps.1,
                               data1.s$sig2.ch.hat.1,data1.s$ID.C,data.1$ID.D,data.1$ID.C,data.1$x,A,t,
                               parameter=c("MEAN"),residual.1=c("unconditional"))$F11
          list(F11.True=F11.True)
        }
        F11[s,]<-colMeans(r.FGT$F11.True)
        F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)  
        F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
        F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
        CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        
      }
      
      if (parameter=="DF"){
        
        if (length(t)==1){
          F.True[s,]<-tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
            F11.True<-ELL.NPB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,eta.1,data1.s$eps.1,
                                 data1.s$sig2.ch.hat.1,data1.s$ID.C,data.1$ID.D,data.1$ID.C,data.1$x,A,t,
                                 parameter=c("DF"),residual.1=c("unconditional"))$F11
            list(F11.True=F11.True)
          }
          F11[s,]<-colMeans(r.FGT$F11.True)
          F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)  
          F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
          
        }
        
        if (length(t)>1){
          F.True[s,,]<-array(matrix(simplify2array(tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t)))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
            F11.True<-ELL.NPB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,eta.1,data1.s$eps.1,
                                 data1.s$sig2.ch.hat.1,data1.s$ID.C,data.1$ID.D,data.1$ID.C,data.1$x,A,t,
                                 parameter=c("DF"),residual.1=c("conditional"))$F11
            list(F11.True=F11.True)
          }
          
          F11[s,,]<-colMeans(r.FGT$F11.True,dims=1)
          F11.MSE[s,,]<-apply(r.FGT$F11.True,c(2,3),sd)
          F11.Q.02.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,,]<-(F.True[s,,]>=F11.Q.02.5 & F.True[s,,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        }
      }
       
      
    } # ELL.NPB.HT End
    
    if (skedasticity=="Heteroskedastic" & Bootstrap=="NPB" & residual.1=="conditional"){
      
      # Heteroskedastic variance components: Using Logistic Function
      gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.1,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      if (parameter=="MEAN"){
        F.True[s,]<-tapply(data.1$y,data.1$ID.D,mean)
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-ELL.NPB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,eta.1,data1.s$eps.1,
                               data1.s$sig2.ch.hat.1,data1.s$ID.C,data.1$ID.D,data.1$ID.C,data.1$x,A,t,
                               parameter=c("MEAN"),residual.1=c("conditional"))$F11
          list(F11.True=F11.True)
        }
        F11[s,]<-colMeans(r.FGT$F11.True)
        F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)  
        F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
        F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
        CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        
      }
      
      if (parameter=="DF"){

          if (length(t)==1){
          F.True[s,]<-tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
            F11.True<-ELL.NPB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,eta.1,data1.s$eps.1,
                                 data1.s$sig2.ch.hat.1,data1.s$ID.C,data.1$ID.D,data.1$ID.C,data.1$x,A,t,
                                 parameter=c("DF"),residual.1=c("conditional"))$F11
            list(F11.True=F11.True)
          }
          F11[s,]<-colMeans(r.FGT$F11.True)
          F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)  
          F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
          
        }
        
        if (length(t)>1){
          F.True[s,,]<-array(matrix(simplify2array(tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t)))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
            F11.True<-ELL.NPB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,eta.1,data1.s$eps.1,
                                 data1.s$sig2.ch.hat.1,data1.s$ID.C,data.1$ID.D,data.1$ID.C,data.1$x,A,t,
                                 parameter=c("DF"),residual.1=c("conditional"))$F11
            list(F11.True=F11.True)
          }
          
          F11[s,,]<-colMeans(r.FGT$F11.True,dims=1)
          F11.MSE[s,,]<-apply(r.FGT$F11.True,c(2,3),sd)
          F11.Q.02.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,,]<-(F.True[s,,]>=F11.Q.02.5 & F.True[s,,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        }
      }
       
      
    } # ELL.NPB.HT End
    
    
  } # Simulation End
  
  list(Sigma.HM=Sigma.HM,Sigma.HT=Sigma.HT,#sigma2.ch.U=sigma2.ch.U,sigma2.ch.U.ELL=sigma2.ch.U.1,
       F.True=F.True,F11=F11,F11.MSE=F11.MSE,CR.I=CR.I)
  
} # Function End
# ------------------------------------------------------------------------------
# Function for Simulation Study: Type-I - Mean & DF : CD Methods
# ------------------------------------------------------------------------------
Simulation.CD.SADF<-function(N.Area,N.Cluster,C.d.s,N.c.s,df,sig2.eta,Prob.C,het.func=c("f1","f2","f3","f4","f4b"),skedasticity=c("Homoskedastic","Heteroskedastic"),Bootstrap=c("SM","MC"),residual.1=c("Fixed","Random"),
                                              het.est.method=c("LPR","STR","ELL"),strata.quantiles,quant,parameter=c("MEAN","DF"),No.Boot,No.Sim){
  
  # The function is based on naive raw residuals
  # For sclaed case: Scale the raw residuals with the corresponding variance 
  # In thesis the scaled version is emphasize
  
  # Population structure
  D<-length(N.Area)
  No.Area<-D
  C<-length(N.Cluster)
  N<-sum(N.Cluster)
  N.d<-N.Area
  N.c<-N.Cluster
  
  ID.D<-rep(1:D,N.d)
  ID.C<-rep(1:C,N.c)
  ID.H<-c(1:N)
  
  # Sample structure
  # C.d.s   # Number of cluster per small area in  sample
  # N.c.s   # Number of individuals per small cluster in  sample 
  
  n<-sum(N.c.s)
  trials<-No.Sim
  Sigma.HM<-matrix(0,trials,2)
  Sigma.HT<-matrix(0,trials,2)
  Sigma.HT.IGLS<-matrix(0,trials,2)
  
  # Individual-specific variance components : Sample
  
  sigma2.ch.s<-matrix(0,n,trials)                                 # True 
  sigma2.ch.s.2<-matrix(0,n,trials)                               # Estimated
  
  #  if (het.est.method=="LPR")  sigma2.ch.s.2<-matrix(0,n,trials)   # Using LOESS (degree 1) method
  #  if (het.est.method=="STR")  sigma2.ch.s.2<-matrix(0,n,trials)   # Using Stratification method
  #  if (het.est.method=="ELL")  sigma2.ch.s.2<-matrix(0,n,trials)   # Using ELL Estimator
  
  # Individual-specific variance components : Population
  
  sigma2.ch.U<-matrix(0,N,trials)                                # True 
  sigma2.ch.U.2<-matrix(0,N,trials)                              # Estimated
  
  #  if (het.est.method=="LPR") sigma2.ch.U.2<-matrix(0,N,trials)   # Using LOESS (degree 1) method
  #  if (het.est.method=="STR") sigma2.ch.U.2<-matrix(0,N,trials)   # Using Stratification method
  #  if (het.est.method=="ELL") sigma2.ch.U.2<-matrix(0,N,trials)   # ELL Estimator
  
  No.Q=ifelse(parameter=="MEAN",1,length(quant))
  
  if (No.Q==1) {
    
    F.True<-array(0,dim=c(trials,No.Area))  # True estimates: SADF 
    F11<-array(0,dim=c(trials,No.Area))     # ELL estimates: SADF
    F11.MSE<-array(0,dim=c(trials,No.Area)) # MSE of ELL estimates: SADF
    CR.I<-array(0,dim=c(trials,No.Area))    # Coverage Indicator of 95% CI  
    
  }
  
  
  if (No.Q>1) {
    
    F.True<-array(0,dim=c(trials,No.Area,No.Q))    # True estimates: FGT 0
    F11<-array(0,dim=c(trials,No.Area,No.Q))       # ELL estimates FGT 0: PB
    F11.MSE<-array(0,dim=c(trials,No.Area,No.Q))   # ELL estimates FGT 0: PB
    CR.I<-array(0,dim=c(trials,No.Area,No.Q))      # Coverage Indicator of 95% CI  
  }
  
  # Parallel Object Creation
  
  # The foreach command is used for the Bootstrap work (Inner loop)
  
  # f2 is for single quantile
  f2 <- function(obj1,obj2) {
    z <- list(
      F11.True=rbind(obj1$F11.True,obj2$F11.True)
    )
  }
  
  # f2.array is for multiple quantile
  
  f2.array <- function(obj1,obj2) {
    z <- list(
      F11.True=abind(obj1$F11.True,obj2$F11.True,along=1)
    )
  }
  
  # Simulation study strat from here 
  
  for (s in 1:trials){
    
    cat(date(),"Iteration number",s,"starting","\n",fill=T)
    
    # Generating explanatory variable
    
    x.ch<-rchisq(N,df)
    
    # Generating cluster-specific random errors 
    
    eta.c<-rnorm(C,0,sqrt(sig2.eta))
    
    # Generating individual-specific random errors 
    
    if (het.func=="f1") sig2.ch<-sig2.ch.1(x.ch)
    if (het.func=="f2") sig2.ch<-sig2.ch.2(x.ch)
    if (het.func=="f3") sig2.ch<-sig2.ch.3(x.ch)
    
    if (het.func=="f4") {
      z.ch<-rbinom(N,1,Prob.C)
      sig2.ch<-sig2.ch.4(x.ch,z.ch)
    }
    
    if (het.func=="f4b") {
      z.ch<-rbinom(N,1,Prob.C)
      sig2.ch<-sig2.ch.4(x.ch,z.ch)
    }
    
    eps.ch<-rnorm(N,0,sqrt(sig2.ch))
    
    # Generating response values for individuals 
    
    y.ch<-500+1.5*x.ch+rep(eta.c,N.c)+eps.ch
    
    data.1<-data.frame(ID.D=ID.D,ID.C=ID.C,ID.H=ID.H,x=x.ch,y=y.ch,sig2.ch=sig2.ch)
    
    if (parameter=="MEAN") t<-mean(data.1$y) else t<-as.vector(quantile(data.1$y,quant))
    
    # Draw the sample from the population
    
    EA.sample=NULL
    
    for (d in 1:D){
      if (length(C.d.s)==1) id.EA.sample=sort(sample(unique(ID.C[ID.D==d]),C.d.s)) # Randomly selection of 2 EAs from each small area & sorted
      if (length(C.d.s)>1) id.EA.sample=sort(sample(unique(ID.C[ID.D==d]),C.d.s[d])) # Randomly selection of 2 EAs from each small area & sorted
      EA.sample<-c(EA.sample,id.EA.sample)
    }
    
    ID.sample<-NULL
    
    for (a in 1:length(EA.sample)){
      if (length(N.c.s)==1)  ID.s<-sort(sample(ID.H[ID.C==EA.sample[a]],N.c.s))
      if (length(N.c.s)>1)  ID.s<-sort(sample(ID.H[ID.C==EA.sample[a]],N.c.s[a]))
      
      if (length(N.c.s)==1 & het.func=="f4b")  ID.s<-sort(sample(ID.H[ID.C==EA.sample[a] & z.ch==0],N.c.s))
      if (length(N.c.s)>1 & het.func=="f4b")  ID.s<-sort(sample(ID.H[ID.C==EA.sample[a] & z.ch==0],N.c.s[a]))
      
      ID.sample<-c(ID.sample,ID.s)
    }
    
    data1.s<-data.1[ID.sample,]
    
    n<-length(data1.s$y)
    n.c<-tapply(data1.s$ID.H,data1.s$ID.C,length)
    number.cluster.s<-length(unique(data1.s$ID.C))
    ID.cluster.s<-unique(data1.s$ID.C)
    
    # Fit the OLS model
    
    lm1<-lm(y~x,data1.s)
    data1.s$uch.1<-resid(lm1)
    eta.1<-as.vector(tapply(data1.s$uch.1,data1.s$ID.C,mean))
    data1.s$eps.1<-data1.s$uch.1-rep(eta.1,n.c)
    data1.s$y.hat<-fitted.values(lm1)
    
    # Estimation of variance  component at level 2 assumong homo.. and hete.. at level one   
    
    sig2.HM.1<-Var.Com.MM.2(data1.s$ID.C,data1.s$ID.H,eta.1,data1.s$uch.1)   # Homoskedasticity at individual level
    sig2.HT.1<-Var.Com.MM.2.H(data1.s$ID.C,data1.s$ID.H,eta.1,data1.s$eps.1) # Heteroskedasticity at individual level
    sig2.HT.1$sigma2.1<-(summary(lm1)$sigma)^2-sig2.HT.1$sigma2.2
    # Residual Variance estimates at level one ==================================================================== 
    
    # Estimation based on LOESS estimates (Degree 1) 
    
    if (het.est.method=="LPR") {
      
      loess.fit.initial<-fANCOVA::loess.as(data1.s$x, data1.s$eps.1^2, degree = 1, criterion = c("gcv"), family = c("gaussian"))
      band.width.loess<-loess.fit.initial$par$span
      
      sigma2.loess<-loess(eps.1^2~x, data=data1.s,span=band.width.loess,family = "gaussian",method = c("loess"),
                          control = loess.control(surface = "interpolate"),degree=1,model = TRUE)
      
      #sigma2.loess.1 <- loess(eps.1^2~x, data=data1.s,span=band.width.loess,family = "gaussian",method = c("loess"),
      #                        control = loess.control(surface = "direct"),degree=1,model = TRUE)
      
      sigma2.x.s.loess<-predict(sigma2.loess, data.frame(x=data1.s$x), se = FALSE)
      sigma2.x.U.loess<-predict(sigma2.loess, data.frame(x=data.1$x), se = FALSE)
      
      sigma2.x.U.min<-predict(sigma2.loess, data.frame(x=min(data1.s$x)), se = FALSE)
      sigma2.x.U.max<-predict(sigma2.loess, data.frame(x=max(data1.s$x)), se = FALSE)
      
      # Estimated results for individuals: LOESS
      data1.s$sig2.ch.hat.2<-sigma2.x.s.loess
      
      data.1$sig2.ch.hat.2<-sigma2.x.U.loess
      data.1$sig2.ch.hat.2[data.1$x<min(data1.s$x)]<-sigma2.x.U.min
      data.1$sig2.ch.hat.2[data.1$x>max(data1.s$x)]<-sigma2.x.U.max
      
    }
    
    # estimates based on Stratification method
    
    if (het.est.method=="STR") {
      
      results.IGLS<-RES.VAR.STRATA.IGLS(data1.s$y,data1.s$x,data1.s$ID.C,data1.s$ID.H,data.1$x,data.1$ID.C,data.1$ID.H,strata.quantiles,Iteration.no=100,tol=1e-20)
      
      data1.s$sig2.ch.hat.2<-results.IGLS$sig2.ch.hat.s
      data.1$sig2.ch.hat.2<-results.IGLS$sig2.ch.hat.U
      
    }
    
    if (het.est.method=="ELL") {
      
      # ELL estimates 
      
      Sigma2.ch.ELL<-sigma2.ch.ELL(data1.s$eps.1,data1.s$x,data.1$x)
      alpha.hat<-Sigma2.ch.ELL$alpha
      cov.alpha.hat<-Sigma2.ch.ELL$vcov.alpha
      A<-Sigma2.ch.ELL$A
      sigma2.alpha<-Sigma2.ch.ELL$sigma2.alpha
      
      # Estimated results for individuals: ELL
      
      data1.s$sig2.ch.hat.2<-Sigma2.ch.ELL$sigma2.ch.s
      data.1$sig2.ch.hat.2<-Sigma2.ch.ELL$sigma2.ch.U
      
    }
    
    # Store the Variance components
    
    Sigma.HM[s,]<-c(sig2.HM.1$sigma2.2,sig2.HM.1$sigma2.1)
    Sigma.HT[s,]<-c(sig2.HT.1$sigma2.2,((summary(lm1)$sigma)^2-sig2.HT.1$sigma2.2))
    if (het.est.method=="STR") Sigma.HT.IGLS[s,]<-c(results.IGLS$sigma2.2.HT.IGLS,((summary(lm1)$sigma)^2-results.IGLS$sigma2.2.HT.IGLS))
    
    sigma2.ch.s[,s]<-data1.s$sig2.ch # True 
    sigma2.ch.s.2[,s]<-data1.s$sig2.ch.hat.2 # Estimated
    
    sigma2.ch.U[,s]<-data.1$sig2.ch # True 
    sigma2.ch.U.2[,s]<-data.1$sig2.ch.hat.2 # Estimated
    
    #    if (het.est.method=="LPR") sigma2.ch.s.2[,s]<-data1.s$sig2.ch.hat.2 # LOESS Smooth function
    #    if (het.est.method=="STR") sigma2.ch.s.2[,s]<-data1.s$sig2.ch.hat.2 # Stratified Smooth Method
    
    #    if (het.est.method=="LPR") sigma2.ch.U.2[,s]<-data.1$sig2.ch.hat.2 # LOESS Smooth function
    #    if (het.est.method=="STR") sigma2.ch.U.2[,s]<-data.1$sig2.ch.hat.2 # Stratified Smooth Method
    
    # Generalized least square estimates of the regression parameters
    
    X.ols<-cbind(rep(1,n),data1.s$x)
    
    # SADF using CD method: Smearing and MC Simulation Approach with HT estimates using LOESS method
    
    # Estimation using CD Smearing approach with Homoskedastic variance components at both level
    
    
    if (skedasticity=="Homoskedastic" & Bootstrap=="SM" & residual.1=="Fixed"){
      
      # Homoskedastic variance components
      
      gls.estimate<-GLS.EST(n.c,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c)
      
      if (parameter=="MEAN"){
        F.True[s,]<-tapply(data.1$y,data.1$ID.D,mean)
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-CD.SM.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,
                             data.1$ID.D,data.1$ID.C,data.1$x,t,parameter="MEAN",residual.1="Fixed")$F11
          list(F11.True=F11.True)
        }
        F11[s,]<-colMeans(r.FGT$F11.True)
        F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)   
        F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
        F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
        CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        
      }
      
    if (parameter=="DF"){
        
      if (length(t)==1){
        
        F.True[s,]<-tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-CD.SM.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,
                    data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("DF"),residual.1="Fixed")$F11
          list(F11.True=F11.True)
        }
        F11[s,]<-colMeans(r.FGT$F11.True)
        F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)   
        F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
        F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
        CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        
      }
      
      if (length(t)>1){
        F.True[s,,]<-array(matrix(simplify2array(tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t)))
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-CD.SM.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,
                             data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("DF"),residual.1="Fixed")$F11
          list(F11.True=F11.True)
        }
        
        F11[s,,]<-colMeans(r.FGT$F11.True,dims=1)
        F11.MSE[s,,]<-apply(r.FGT$F11.True,c(2,3),sd)
        F11.Q.02.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
        F11.Q.97.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
        CR.I[s,,]<-(F.True[s,,]>=F11.Q.02.5 & F.True[s,,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
       } 
      
    }
     
  }# CD.SM.HM.Scale with Fixed residuals
    
    if (skedasticity=="Homoskedastic" & Bootstrap=="SM" & residual.1=="Random"){
      
      # Homoskedastic variance components
      
      gls.estimate<-GLS.EST(n.c,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c)
      
      if (parameter=="MEAN"){
        F.True[s,]<-tapply(data.1$y,data.1$ID.D,mean)
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-CD.SM.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,
                             data.1$ID.D,data.1$ID.C,data.1$x,t,parameter="MEAN",residual.1="Random")$F11
          list(F11.True=F11.True)
        }
        F11[s,]<-colMeans(r.FGT$F11.True)
        F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)   
        F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
        F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
        CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      }
      
      if (parameter=="DF"){
        if (length(t)==1){
          F.True[s,]<-tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
            F11.True<-CD.SM.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,
                               data.1$ID.D,data.1$ID.C,data.1$x,t,parameter="DF",residual.1="Random")$F11
            list(F11.True=F11.True)
          }
          F11[s,]<-colMeans(r.FGT$F11.True)
          F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)   
          F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        }
        
        if (length(t)>1){
          F.True[s,,]<-array(matrix(simplify2array(tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t)))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
            F11.True<-CD.SM.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,
                               data.1$ID.D,data.1$ID.C,data.1$x,t,parameter="DF",residual.1="Random")$F11
            list(F11.True=F11.True)
          }
          F11[s,,]<-colMeans(r.FGT$F11.True,dims=1)
          F11.MSE[s,,]<-apply(r.FGT$F11.True,c(2,3),sd)
          F11.Q.02.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,,]<-(F.True[s,,]>=F11.Q.02.5 & F.True[s,,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        }
      }
    } # CD.SM.HM.Scale with Random residuals
    
    if (skedasticity=="Heteroskedastic" & Bootstrap=="SM" & residual.1=="Fixed"){
      
      # Heteroskedastic variance components
      gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c)
      
      # Standardized the level one residuals
      #std.eps.s<-data1.s$eps.1.gls/sqrt(data1.s$sig2.ch.hat.2)
      
      # Smearing term
      # eps.u.l <- outer(sqrt(data.1$sig2.ch.hat.2),std.eps.s)
      

      if (parameter=="MEAN"){
        F.True[s,]<-tapply(data.1$y,data.1$ID.D,mean)
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-CD.SM.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,
                             data1.s$sig2.ch.hat.2,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("MEAN"),residual.1="Fixed")$F11
          list(F11.True=F11.True)
        } 
        F11[s,]<-colMeans(r.FGT$F11.True)
        F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)  
        F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
        F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
        CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        
      }      
      
      if (parameter=="DF"){
        
       if (length(t)==1){
        F.True[s,]<-tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-CD.SM.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,
                    data1.s$sig2.ch.hat.2,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("DF"),residual.1="Fixed")$F11
          list(F11.True=F11.True)
        } 
        F11[s,]<-colMeans(r.FGT$F11.True)
        F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)  
        F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
        F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
        CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        
      }
      
      if (length(t)>1){
        F.True[s,,]<-array(matrix(simplify2array(tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t)))
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-CD.SM.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,
                             data1.s$sig2.ch.hat.2,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter="DF",residual.1="Fixed")$F11
          list(F11.True=F11.True)
        }
        
        F11[s,,]<-colMeans(r.FGT$F11.True,dims=1)
        F11.MSE[s,,]<-apply(r.FGT$F11.True,c(2,3),sd)
        F11.Q.02.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
        F11.Q.97.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
        CR.I[s,,]<-(F.True[s,,]>=F11.Q.02.5 & F.True[s,,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      }
    }    
      
    } # CD.SM.HT.Scale with Fixed residuals
   
    if (skedasticity=="Heteroskedastic" & Bootstrap=="SM" & residual.1=="Random"){
      
      # Heteroskedastic variance components
      gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c)
      
      # Standardized the level one residuals
      #std.eps.s<-data1.s$eps.1.gls/sqrt(data1.s$sig2.ch.hat.2)
      
      # Smearing term
      # eps.u.l <- outer(sqrt(data.1$sig2.ch.hat.2),std.eps.s)
      
      
      if (parameter=="MEAN"){
        F.True[s,]<-tapply(data.1$y,data.1$ID.D,mean)
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-CD.SM.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,
                             data1.s$sig2.ch.hat.2,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("MEAN"),residual.1="Random")$F11
          list(F11.True=F11.True)
        } 
        F11[s,]<-colMeans(r.FGT$F11.True)
        F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)  
        F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
        F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
        CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        
      }      
      
      if (parameter=="DF"){
        
        if (length(t)==1){
          F.True[s,]<-tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
            F11.True<-CD.SM.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,
                               data1.s$sig2.ch.hat.2,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("DF"),residual.1="Random")$F11
            list(F11.True=F11.True)
          } 
          F11[s,]<-colMeans(r.FGT$F11.True)
          F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)  
          F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
          
        }
        
        if (length(t)>1){
          F.True[s,,]<-array(matrix(simplify2array(tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t)))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
            F11.True<-CD.SM.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,
                               data1.s$sig2.ch.hat.2,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter="DF",residual.1="Random")$F11
            list(F11.True=F11.True)
          }
          
          F11[s,,]<-colMeans(r.FGT$F11.True,dims=1)
          F11.MSE[s,,]<-apply(r.FGT$F11.True,c(2,3),sd)
          F11.Q.02.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,,]<-(F.True[s,,]>=F11.Q.02.5 & F.True[s,,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        }
      }    
      
    } # CD.SM.HT.Scale with Fixed residuals
    
    if (skedasticity=="Homoskedastic" & Bootstrap=="MC"){
      
      # Homoskedastic variance components
      
      gls.estimate<-GLS.EST(n.c,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c)
      

      if (parameter=="MEAN"){
          F.True[s,]<-tapply(data.1$y,data.1$ID.D,mean)
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
            F11.True<-CD.MC.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("MEAN"))$F11
            list(F11.True=F11.True)
          } 
          F11[s,]<-colMeans(r.FGT$F11.True)
          F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)    
          F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
          
        }
      
    if (parameter=="DF"){
        if (length(t)==1){
          F.True[s,]<-tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
            F11.True<-CD.MC.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter="DF")$F11
            list(F11.True=F11.True)
          } 
          F11[s,]<-colMeans(r.FGT$F11.True)
          F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)    
          F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
          
        }
        
        if (length(t)>1){
          F.True[s,,]<-array(matrix(simplify2array(tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t)))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
            F11.True<-CD.MC.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter="DF")$F11
            list(F11.True=F11.True)
          }
          
          F11[s,,]<-colMeans(r.FGT$F11.True,dims=1)
          F11.MSE[s,,]<-apply(r.FGT$F11.True,c(2,3),sd)
          F11.Q.02.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,,]<-(F.True[s,,]>=F11.Q.02.5 & F.True[s,,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        }
      }
    } # CD.MC.HM.Scale 

    if (skedasticity=="Heteroskedastic" & Bootstrap=="MC"){
      
      # Heteroskedastic variance components
      
      gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c)
      
      if (parameter=="MEAN"){
          F.True[s,]<-tapply(data.1$y,data.1$ID.D,mean)
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
            F11.True<-CD.MC.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data1.s$sig2.ch.hat.2,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("MEAN"))$F11
            list(F11.True=F11.True)
          } 
          F11[s,]<-colMeans(r.FGT$F11.True)
          F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)    
          F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
          
      }
      
      if (parameter=="DF"){
        
        if (length(t)==1){
          F.True[s,]<-tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
            F11.True<-CD.MC.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data1.s$sig2.ch.hat.2,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("DF"))$F11
            list(F11.True=F11.True)
          } 
          F11[s,]<-colMeans(r.FGT$F11.True)
          F11.MSE[s,]<-apply(r.FGT$F11.True,2,sd)    
          F11.Q.02.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,2,function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,]<-(F.True[s,]>=F11.Q.02.5 & F.True[s,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
          
        }
        
        if (length(t)>1){
          F.True[s,,]<-array(matrix(simplify2array(tapply(data.1$y,data.1$ID.D,function (x) FGT.alpha(x,t,0))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t)))
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
            F11.True<-CD.MC.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data1.s$sig2.ch.hat.2,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,data.1$x,t,parameter=c("DF"))$F11
            list(F11.True=F11.True)
          }
          
          F11[s,,]<-colMeans(r.FGT$F11.True,dims=1)
          F11.MSE[s,,]<-apply(r.FGT$F11.True,c(2,3),sd)
          F11.Q.02.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
          F11.Q.97.5<-apply(r.FGT$F11.True,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
          CR.I[s,,]<-(F.True[s,,]>=F11.Q.02.5 & F.True[s,,]<=F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
        }  
      }
      
      
    } # CD.MC.HT.Scaled.Residuals 
    
    
  } # Simulation End
  
  list(Sigma.HM=Sigma.HM,Sigma.HT=Sigma.HT,Sigma.HT.IGLS=Sigma.HT.IGLS,#sigma2.ch.U=sigma2.ch.U,sigma2.ch.U.STR=sigma2.ch.U.2,
       F.True=F.True,F11=F11,F11.MSE=F11.MSE,CR.I=CR.I)
  
} # Function End
# ------------------------------------------------------------------------------
# Function for Simulation Study: Type-II - FGT  : ELL Methods
# ------------------------------------------------------------------------------
Simulation.ELL.FGT<-function(N.Area,N.Cluster,C.d.s,N.c.s,beta,Sigma.Mu,Sigma2.X,sig2.eta,Prob.C,het.func=c("f1","f2","f3","f4","f4b"),
                             skedasticity=c("Homoskedastic","Heteroskedastic"),Bootstrap=c("PB","NPB"),residual.1=c("unconditional","conditional"),quant,parameter=c("FGT"),No.Boot,No.Sim){
  
  # Population structure
  D<-length(N.Area); No.Area<-D; C<-length(N.Cluster); N<-sum(N.Cluster); N.d<-N.Area; N.c<-N.Cluster;
  ID.D<-rep(1:D,N.d); ID.C<-rep(1:C,N.c); ID.H<-c(1:N)
  
  # Sample structure # C.d.s: Number of cluster per small area in  sample
  # N.c.s : Number of individuals per small cluster in  sample 
  n<-sum(N.c.s)
  
  trials<-No.Sim ; Sigma.HM<-matrix(0,trials,2); Sigma.HT<-matrix(0,trials,2)
  
  # Individual-specific variance components : Sample
  sigma2.ch.s<-matrix(0,n,trials)     # True 
  sigma2.ch.s.1<-matrix(0,n,trials) # Using ELL logistic method
  
  # Individual-specific variance components : Population
  sigma2.ch.U<-matrix(0,N,trials)     # True 
  sigma2.ch.U.1<-matrix(0,N,trials) # Using ELL logistic method
  
  No.Q=length(quant)
  
  if (No.Q==1) {
    
    F0.True<-array(0,dim=c(trials,No.Area))      # True estimates: FGT 0
    F1.True<-array(0,dim=c(trials,No.Area))      # True estimates: FGT 1
    F2.True<-array(0,dim=c(trials,No.Area))      # True estimates: FGT 2
    
    F0.F11<-array(0,dim=c(trials,No.Area))       # ELL estimates FGT 0
    F1.F11<-array(0,dim=c(trials,No.Area))       # ELL estimates FGT 1
    F2.F11<-array(0,dim=c(trials,No.Area))       # ELL estimates FGT 2
    
    F0.F11.MSE<-array(0,dim=c(trials,No.Area))   # MSE of estimated FGT 0
    F1.F11.MSE<-array(0,dim=c(trials,No.Area))   # MSE of estimated FGT 1
    F2.F11.MSE<-array(0,dim=c(trials,No.Area))   # MSE of estimated FGT 2
    
    F0.CR.I<-array(0,dim=c(trials,No.Area))      # Coverage Indicator of 95% CI  
    F1.CR.I<-array(0,dim=c(trials,No.Area))      # Coverage Indicator of 95% CI  
    F2.CR.I<-array(0,dim=c(trials,No.Area))      # Coverage Indicator of 95% CI  
    
  }
  
  if (No.Q>1) {
    
    F0.True<-array(0,dim=c(trials,No.Area,No.Q))      # True estimates: FGT 0
    F1.True<-array(0,dim=c(trials,No.Area,No.Q))      # True estimates: FGT 1
    F2.True<-array(0,dim=c(trials,No.Area,No.Q))      # True estimates: FGT 2
    
    F0.F11<-array(0,dim=c(trials,No.Area,No.Q))       # ELL estimates FGT 0
    F1.F11<-array(0,dim=c(trials,No.Area,No.Q))       # ELL estimates FGT 1
    F2.F11<-array(0,dim=c(trials,No.Area,No.Q))       # ELL estimates FGT 2
    
    F0.F11.MSE<-array(0,dim=c(trials,No.Area,No.Q))   # MSE of estimated FGT 0
    F1.F11.MSE<-array(0,dim=c(trials,No.Area,No.Q))   # MSE of estimated FGT 1
    F2.F11.MSE<-array(0,dim=c(trials,No.Area,No.Q))   # MSE of estimated FGT 2
    
    F0.CR.I<-array(0,dim=c(trials,No.Area,No.Q))      # Coverage Indicator of 95% CI  
    F1.CR.I<-array(0,dim=c(trials,No.Area,No.Q))      # Coverage Indicator of 95% CI  
    F2.CR.I<-array(0,dim=c(trials,No.Area,No.Q))      # Coverage Indicator of 95% CI  
    
  }
  
  # Parallel Object Creation # The foreach command is used for the Bootstrap work (Inner loop)
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      F11.FGT0=rbind(obj1$F11.FGT0,obj2$F11.FGT0),
      F11.FGT1=rbind(obj1$F11.FGT1,obj2$F11.FGT1),
      F11.FGT2=rbind(obj1$F11.FGT2,obj2$F11.FGT2)
    )
  }
  f2.array <- function(obj1,obj2) {
    # f2.array is for multiple quantile
    z <- list(
      F11.FGT0=abind(obj1$F11.FGT0,obj2$F11.FGT0,along=1),
      F11.FGT1=abind(obj1$F11.FGT1,obj2$F11.FGT1,along=1),
      F11.FGT2=abind(obj1$F11.FGT2,obj2$F11.FGT2,along=1)
    )
  }
  
  # Simulation study strat from here 
  
  for (s in 1:trials){
    
    cat(date(),"Iteration number",s,"starting","\n",fill=T)
    
    # Generating explanatory variable ========================================
    
    X<-rmvnorm(N,Sigma.Mu,Sigma2.X)
    X.beta<-cbind(rep(1,dim(X)[1]),X)%*%beta
    
    
    eta.c<-rnorm(C,0,sqrt(sig2.eta))  # Generating cluster-specific random errors 
    
    # Generating individual-specific random errors 
    if (het.func=="f1") sig2.ch<-sig2.ch.1(X.beta)
    if (het.func=="f2") sig2.ch<-sig2.ch.2(X.beta)
    if (het.func=="f3") sig2.ch<-sig2.ch.3(X.beta)
    if (het.func=="f4") {
      z.ch<-rbinom(N,1,Prob.C)
      sig2.ch<-sig2.ch.4(X.beta,z.ch)
    }
    if (het.func=="f4b") {
      z.ch<-rbinom(N,1,Prob.C)
      sig2.ch<-sig2.ch.4(X.beta,z.ch)
    }
    
    eps.ch<-rnorm(N,0,sqrt(sig2.ch))
    
    # Generating response values for individuals 
    log.y.ch<-X.beta+rep(eta.c,N.c)+eps.ch
    
    data.1<-data.frame(ID.D=ID.D,ID.C=ID.C,ID.H=ID.H,x1=X[,1],x2=X[,2],y=log.y.ch,sig2.ch=sig2.ch)
    t<-as.vector(quantile(exp(data.1$y),quant))
    
    EA.sample=NULL     # Draw the sample from the population
    for (d in 1:D){
      if (length(C.d.s)==1) id.EA.sample=sort(sample(unique(ID.C[ID.D==d]),C.d.s)) # Randomly selection of 2 EAs from each small area & sorted
      if (length(C.d.s)>1) id.EA.sample=sort(sample(unique(ID.C[ID.D==d]),C.d.s[d])) # Randomly selection of 2 EAs from each small area & sorted
      EA.sample<-c(EA.sample,id.EA.sample)
    }
    
    ID.sample<-NULL
    for (a in 1:length(EA.sample)){
      if (length(N.c.s)==1) ID.s<-sort(sample(ID.H[ID.C==EA.sample[a]],N.c.s))
      if (length(N.c.s)>1)  ID.s<-sort(sample(ID.H[ID.C==EA.sample[a]],N.c.s[a]))
      
      if (length(N.c.s)==1 & het.func=="f4b")  ID.s<-sort(sample(ID.H[ID.C==EA.sample[a] & z.ch==0],N.c.s))
      if (length(N.c.s)>1 & het.func=="f4b")  ID.s<-sort(sample(ID.H[ID.C==EA.sample[a] & z.ch==0],N.c.s[a]))
      
      ID.sample<-c(ID.sample,ID.s)
    }
    
    data1.s<-data.1[ID.sample,]
    n<-length(data1.s$y)
    n.c<-tapply(data1.s$ID.H,data1.s$ID.C,length)
    number.cluster.s<-length(unique(data1.s$ID.C))
    ID.cluster.s<-unique(data1.s$ID.C)
    
    lm1<-lm(y~x1+x2,data1.s) # Fit the OLS model
    data1.s$uch.1<-resid(lm1)
    eta.1<-as.vector(tapply(data1.s$uch.1,data1.s$ID.C,mean))
    data1.s$eps.1<-data1.s$uch.1-rep(eta.1,n.c)
    data1.s$y.hat<-fitted.values(lm1)
    
    # Estimation of variance  component at level 2 assumong homo.. and hete.. at level one
    sig2.HM.1<-Var.Com.MM.2(data1.s$ID.C,data1.s$ID.H,eta.1,data1.s$uch.1)   # Homoskedasticity at individual level
    sig2.HT.1<-Var.Com.MM.2.H(data1.s$ID.C,data1.s$ID.H,eta.1,data1.s$eps.1) # Heteroskedasticity at individual level
    
    # Explanatory variables for Census and san=mple observations
    X.s<-cbind(data1.s$x1,data1.s$x2)
    X.U<-cbind(data.1$x1,data.1$x2)
    
    Sigma2.ch.ELL<-sigma2.ch.ELL(data1.s$eps.1,X.s,X.U)     # ELL estimates 
    alpha.hat<-Sigma2.ch.ELL$alpha
    cov.alpha.hat<-Sigma2.ch.ELL$vcov.alpha
    A<-Sigma2.ch.ELL$A
    sigma2.alpha<-Sigma2.ch.ELL$sigma2.alpha
    
    # Estimated results for individuals: ELL
    data1.s$sig2.ch.hat.1<-Sigma2.ch.ELL$sigma2.ch.s
    data.1$sig2.ch.hat.1<-Sigma2.ch.ELL$sigma2.ch.U
    
    # Store the Variance components
    Sigma.HM[s,]<-c(sig2.HM.1$sigma2.2,sig2.HM.1$sigma2.1)
    Sigma.HT[s,]<-c(sig2.HT.1$sigma2.2,((summary(lm1)$sigma)^2-sig2.HT.1$sigma2.2))
    
    sigma2.ch.s[,s]<-data1.s$sig2.ch # True for sample observations
    sigma2.ch.s.1[,s]<-data1.s$sig2.ch.hat.1 # Using logistic method for sample observations
    
    sigma2.ch.U[,s]<-data.1$sig2.ch # True for Population observations
    sigma2.ch.U.1[,s]<-data.1$sig2.ch.hat.1 # Using logistic method for Population observations
    
    # Explanatory variables for Sample and Population units
    
    X.ols<-cbind(rep(1,n),data1.s$x1,data1.s$x2)
    
    
    # FGT Estimation using ELL Method ===================================================================
    
    if (skedasticity=="Homoskedastic" & Bootstrap=="PB"){
      # Estimation using Parametric ELL Method with Homoskedastic variance components at both level
      
      gls.estimate<-GLS.EST(n.c,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      if (length(t)==1){
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-ELL.PB.HM(beta.gls,var.beta.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      }
      
      if (length(t)>1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-ELL.PB.HM(beta.gls,var.beta.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      } 
      
    }  # ELL.PB.HM.FGT End
    
    if (skedasticity=="Heteroskedastic" & Bootstrap=="PB"){
      
      # Heteroskedastic variance components: Using Logistic Function
      gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.1,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      if (length(t)==1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-ELL.PB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,sig2.HT.1$sigma2.2,data.1$ID.D,data.1$ID.C,X.U,A,t,parameter="FGT")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }  
      }
      
      if (length(t)>1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-ELL.PB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,sig2.HT.1$sigma2.2,data.1$ID.D,data.1$ID.C,X.U,A,t,parameter="FGT")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }  
      }
      
    } # ELL.PB.HT.FGT End
    
    if (skedasticity=="Homoskedastic" & Bootstrap=="NPB" & residual.1=="unconditional"){
      
      gls.estimate<-GLS.EST(n.c,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      if (length(t)==1){    
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-ELL.NPB.HM(beta.gls,var.beta.gls,eta.1,data1.s$eps.1,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data1.s$ID.C,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1=c("unconditional"))
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      }
      
      if (length(t)>1){
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-ELL.NPB.HM(beta.gls,var.beta.gls,eta.1,data1.s$eps.1,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data1.s$ID.C,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1=c("unconditional"))
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }    
      } 
      
    } # ELL.NPB.HM.FGT End
    
    if (skedasticity=="Homoskedastic" & Bootstrap=="NPB" & residual.1=="conditional"){
      
      gls.estimate<-GLS.EST(n.c,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      if (length(t)==1){    
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-ELL.NPB.HM(beta.gls,var.beta.gls,eta.1,data1.s$eps.1,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data1.s$ID.C,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1=c("conditional"))
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      }
      
      if (length(t)>1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-ELL.NPB.HM(beta.gls,var.beta.gls,eta.1,data1.s$eps.1,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data1.s$ID.C,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1=c("conditional"))
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }    
      } 
      
    } # ELL.NPB.HM.FGT End
    ELL.NPB.HT<- function(beta,var.beta,alpha,var.alpha,sigma2.alpha,eta.s,eps.s,
                          sig2.eps.s,ID.C.s,ID.D,ID.C,X.U,A,t,parameter=c("MEAN","DF","FGT"),
                          residual.1=c("unconditional","conditional"))    
      if (skedasticity=="Heteroskedastic" & Bootstrap=="NPB" & residual.1=="unconditional"){
        
        # Heteroskedastic variance components: Using Logistic Function
        gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.1,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
        beta.gls <- gls.estimate$beta.gls
        var.beta.gls<- gls.estimate$vcov.beta.gls
        
        if (length(t)==1){
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
            F11.True<-ELL.NPB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,eta.1,data1.s$eps.1,data1.s$sig2.ch.hat.1,data1.s$ID.C,data.1$ID.D,data.1$ID.C,X.U,A,t,parameter="FGT",residual.1=c("unconditional"))
            F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
            F11.True<-NULL
            list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
          }
        }
        
        if (length(t)>1){
          
          r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
            F11.True<-ELL.NPB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,eta.1,data1.s$eps.1,data1.s$sig2.ch.hat.1,data1.s$ID.C,data.1$ID.D,data.1$ID.C,X.U,A,t,parameter="FGT",residual.1=c("unconditional"))
            F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
            F11.True<-NULL
            list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
          }
        } 
        
      } # ELL.NPB.HT.FGT with "Unconditional" Level one Residuals End
    
    if (skedasticity=="Heteroskedastic" & Bootstrap=="NPB" & residual.1=="conditional"){
      
      # Heteroskedastic variance components: Using Logistic Function
      gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.1,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      if (length(t)==1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-ELL.NPB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,eta.1,data1.s$eps.1,data1.s$sig2.ch.hat.1,data1.s$ID.C,data.1$ID.D,data.1$ID.C,X.U,A,t,parameter="FGT",residual.1=c("conditional"))
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      }
      
      if (length(t)>1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-ELL.NPB.HT(beta.gls,var.beta.gls,alpha.hat,cov.alpha.hat,sigma2.alpha,eta.1,data1.s$eps.1,data1.s$sig2.ch.hat.1,data1.s$ID.C,data.1$ID.D,data.1$ID.C,X.U,A,t,parameter="FGT",residual.1=c("conditional"))
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      } 
      
    } # ELL.NPB.HT.FGT with "Conditional" Level one Residuals End
    
    if (length(t)==1){
      
      F0.True[s,]<-tapply(exp(data.1$y),data.1$ID.D,function (x) FGT.alpha(x,t,0)) # True estimates: FGT 0
      F1.True[s,]<-tapply(exp(data.1$y),data.1$ID.D,function (x) FGT.alpha(x,t,1)) # True estimates: FGT 1
      F2.True[s,]<-tapply(exp(data.1$y),data.1$ID.D,function (x) FGT.alpha(x,t,2)) # True estimates: FGT 2
      
      F0.F11[s,]<-colMeans(r.FGT$F11.FGT0) ; F0.F11.MSE[s,]<-apply(r.FGT$F11.FGT0,2,sd)
      F0.F11.Q.02.5<-apply(r.FGT$F11.FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
      F0.F11.Q.97.5<-apply(r.FGT$F11.FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
      F0.CR.I[s,]<-(F0.True[s,]>=F0.F11.Q.02.5 & F0.True[s,]<=F0.F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      
      F1.F11[s,]<-colMeans(r.FGT$F11.FGT1) ; F1.F11.MSE[s,]<-apply(r.FGT$F11.FGT1,2,sd)
      F1.F11.Q.02.5<-apply(r.FGT$F11.FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
      F1.F11.Q.97.5<-apply(r.FGT$F11.FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
      F1.CR.I[s,]<-(F1.True[s,]>=F1.F11.Q.02.5 & F1.True[s,]<=F1.F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      
      F2.F11[s,]<-colMeans(r.FGT$F11.FGT2) ; F2.F11.MSE[s,]<-apply(r.FGT$F11.FGT2,2,sd)
      F2.F11.Q.02.5<-apply(r.FGT$F11.FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
      F2.F11.Q.97.5<-apply(r.FGT$F11.FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
      F2.CR.I[s,]<-(F2.True[s,]>=F2.F11.Q.02.5 & F2.True[s,]<=F2.F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      
    }
    
    if (length(t)>1){
      
      F0.True[s,,]<-array(matrix(simplify2array(tapply(exp(data.1$y),data.1$ID.D,function (x) FGT.alpha(x,t,0))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t))) # True estimates: FGT 0
      F1.True[s,,]<-array(matrix(simplify2array(tapply(exp(data.1$y),data.1$ID.D,function (x) FGT.alpha(x,t,1))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t))) # True estimates: FGT 1
      F2.True[s,,]<-array(matrix(simplify2array(tapply(exp(data.1$y),data.1$ID.D,function (x) FGT.alpha(x,t,2))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t))) # True estimates: FGT 2
      
      F0.F11[s,,]<-colMeans(r.FGT$F11.FGT0,dims=1) ; F0.F11.MSE[s,,]<-apply(r.FGT$F11.FGT0,c(2,3),sd)        
      F0.F11.Q.02.5<-apply(r.FGT$F11.FGT0,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
      F0.F11.Q.97.5<-apply(r.FGT$F11.FGT0,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
      F0.CR.I[s,,]<-(F0.True[s,,]>=F0.F11.Q.02.5 & F0.True[s,,]<=F0.F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      
      F1.F11[s,,]<-colMeans(r.FGT$F11.FGT1,dims=1) ; F1.F11.MSE[s,,]<-apply(r.FGT$F11.FGT1,c(2,3),sd)
      F1.F11.Q.02.5<-apply(r.FGT$F11.FGT1,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
      F1.F11.Q.97.5<-apply(r.FGT$F11.FGT1,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
      F1.CR.I[s,,]<-(F1.True[s,,]>=F1.F11.Q.02.5 & F1.True[s,,]<=F1.F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      
      F2.F11[s,,]<-colMeans(r.FGT$F11.FGT2,dims=1) ; F2.F11.MSE[s,,]<-apply(r.FGT$F11.FGT2,c(2,3),sd)
      F2.F11.Q.02.5<-apply(r.FGT$F11.FGT2,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
      F2.F11.Q.97.5<-apply(r.FGT$F11.FGT2,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
      F2.CR.I[s,,]<-(F2.True[s,,]>=F2.F11.Q.02.5 & F2.True[s,,]<=F2.F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      
    } 
    
  } # Simulation End
  
  list(Sigma.HM=Sigma.HM,Sigma.HT=Sigma.HT,#sigma2.ch.U=sigma2.ch.U,sigma2.ch.U.ELL=sigma2.ch.U.1,
       F0.True=F0.True,F1.True=F1.True,F2.True=F2.True,
       F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.CR.I=F0.CR.I,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.CR.I=F1.CR.I,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.CR.I=F2.CR.I)
  
} # Function End
# ------------------------------------------------------------------------------
# Function for Simulation Study: Type-I - FGT : CD Methods
# ------------------------------------------------------------------------------
Simulation.CD.FGT<-function(N.Area,N.Cluster,C.d.s,N.c.s,beta,Sigma.Mu,Sigma2.X,sig2.eta,Prob.C,het.func=c("f1","f2","f3","f4","f4b"),skedasticity=c("Homoskedastic","Heteroskedastic"),
                                             Bootstrap=c("SM","MC"),residual.1=c("Fixed","Random"),het.est.method=c("LPR","STR"),strata.quantiles,quant,parameter=c("FGT"),No.Boot,No.Sim){
  
  # Population structure
  D<-length(N.Area); No.Area<-D; C<-length(N.Cluster); N<-sum(N.Cluster); N.d<-N.Area; N.c<-N.Cluster
  ID.D<-rep(1:D,N.d) ; ID.C<-rep(1:C,N.c) ; ID.H<-c(1:N) ;
  
  # Sample structure # C.d.s   # Number of cluster per small area in sample # N.c.s   # Number of individuals per small cluster in  sample 
  
  n<-sum(N.c.s)
  trials<-No.Sim
  Sigma.HM<-matrix(0,trials,2) ; Sigma.HT<-matrix(0,trials,2) ; Sigma.HT.IGLS<-matrix(0,trials,2)
  
  # Individual-specific variance components : Sample
  
  sigma2.ch.s<-matrix(0,n,trials)                                 # True 
  if (het.est.method=="LPR")  sigma2.ch.s.2<-matrix(0,n,trials)   # Using LOESS (degree 1) method
  if (het.est.method=="STR")  sigma2.ch.s.2<-matrix(0,n,trials)   # Using Stratification method
  
  # Individual-specific variance components : Population
  
  sigma2.ch.U<-matrix(0,N,trials)                                # True 
  if (het.est.method=="LPR") sigma2.ch.U.2<-matrix(0,N,trials)   # Using LOESS (degree 1) method
  if (het.est.method=="STR") sigma2.ch.U.2<-matrix(0,N,trials)   # Stratification
  
  No.Q=length(quant)
  
  if (No.Q==1) {
    
    F0.True<-array(0,dim=c(trials,No.Area))      # True estimates: FGT 0
    F1.True<-array(0,dim=c(trials,No.Area))      # True estimates: FGT 1
    F2.True<-array(0,dim=c(trials,No.Area))      # True estimates: FGT 2
    
    F0.F11<-array(0,dim=c(trials,No.Area))       # ELL estimates FGT 0
    F1.F11<-array(0,dim=c(trials,No.Area))       # ELL estimates FGT 1
    F2.F11<-array(0,dim=c(trials,No.Area))       # ELL estimates FGT 2
    
    F0.F11.MSE<-array(0,dim=c(trials,No.Area))   # MSE of estimated FGT 0
    F1.F11.MSE<-array(0,dim=c(trials,No.Area))   # MSE of estimated FGT 1
    F2.F11.MSE<-array(0,dim=c(trials,No.Area))   # MSE of estimated FGT 2
    
    F0.CR.I<-array(0,dim=c(trials,No.Area))      # Coverage Indicator of 95% CI  
    F1.CR.I<-array(0,dim=c(trials,No.Area))      # Coverage Indicator of 95% CI  
    F2.CR.I<-array(0,dim=c(trials,No.Area))      # Coverage Indicator of 95% CI  
    
  }
  
  if (No.Q>1) {
    
    F0.True<-array(0,dim=c(trials,No.Area,No.Q))      # True estimates: FGT 0
    F1.True<-array(0,dim=c(trials,No.Area,No.Q))      # True estimates: FGT 1
    F2.True<-array(0,dim=c(trials,No.Area,No.Q))      # True estimates: FGT 2
    
    F0.F11<-array(0,dim=c(trials,No.Area,No.Q))       # ELL estimates FGT 0
    F1.F11<-array(0,dim=c(trials,No.Area,No.Q))       # ELL estimates FGT 1
    F2.F11<-array(0,dim=c(trials,No.Area,No.Q))       # ELL estimates FGT 2
    
    F0.F11.MSE<-array(0,dim=c(trials,No.Area,No.Q))   # MSE of estimated FGT 0
    F1.F11.MSE<-array(0,dim=c(trials,No.Area,No.Q))   # MSE of estimated FGT 1
    F2.F11.MSE<-array(0,dim=c(trials,No.Area,No.Q))   # MSE of estimated FGT 2
    
    F0.CR.I<-array(0,dim=c(trials,No.Area,No.Q))      # Coverage Indicator of 95% CI  
    F1.CR.I<-array(0,dim=c(trials,No.Area,No.Q))      # Coverage Indicator of 95% CI  
    F2.CR.I<-array(0,dim=c(trials,No.Area,No.Q))      # Coverage Indicator of 95% CI  
    
  }
  
  # Parallel Object Creation # The foreach command is used for the Bootstrap work (Inner loop)
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      F11.FGT0=rbind(obj1$F11.FGT0,obj2$F11.FGT0),
      F11.FGT1=rbind(obj1$F11.FGT1,obj2$F11.FGT1),
      F11.FGT2=rbind(obj1$F11.FGT2,obj2$F11.FGT2)
    )
  }

  f2.array <- function(obj1,obj2) {
    # f2.array is for multiple quantile
    z <- list(
      F11.FGT0=abind(obj1$F11.FGT0,obj2$F11.FGT0,along=1),
      F11.FGT1=abind(obj1$F11.FGT1,obj2$F11.FGT1,along=1),
      F11.FGT2=abind(obj1$F11.FGT2,obj2$F11.FGT2,along=1)
    )
  }
  # Simulation study strat from here 
  
  for (s in 1:trials){
    
    cat(date(),"Iteration number",s,"starting","\n",fill=T)
    
    # Generating explanatory variable ========================================
    
    X<-rmvnorm(N,Sigma.Mu,Sigma2.X)
    X.beta<-cbind(rep(1,dim(X)[1]),X)%*%beta
    
    
    eta.c<-rnorm(C,0,sqrt(sig2.eta))  # Generating cluster-specific random errors 
    
    # Generating individual-specific random errors 
    if (het.func=="f1") sig2.ch<-sig2.ch.1(X.beta)
    if (het.func=="f2") sig2.ch<-sig2.ch.2(X.beta)
    if (het.func=="f3") sig2.ch<-sig2.ch.3(X.beta)
    if (het.func=="f4") {
      z.ch<-rbinom(N,1,Prob.C)
      sig2.ch<-sig2.ch.4(X.beta,z.ch)
    }
    if (het.func=="f4b") {
      z.ch<-rbinom(N,1,Prob.C)
      sig2.ch<-sig2.ch.4(X.beta,z.ch)
    }
    
    eps.ch<-rnorm(N,0,sqrt(sig2.ch))
    
    # Generating response values for individuals 
    log.y.ch<-X.beta+rep(eta.c,N.c)+eps.ch
    
    data.1<-data.frame(ID.D=ID.D,ID.C=ID.C,ID.H=ID.H,x1=X[,1],x2=X[,2],y=log.y.ch,sig2.ch=sig2.ch)
    t<-as.vector(quantile(exp(data.1$y),quant))
    
    EA.sample=NULL     # Draw the sample from the population
    for (d in 1:D){
      if (length(C.d.s)==1) id.EA.sample=sort(sample(unique(ID.C[ID.D==d]),C.d.s)) # Randomly selection of 2 EAs from each small area & sorted
      if (length(C.d.s)>1) id.EA.sample=sort(sample(unique(ID.C[ID.D==d]),C.d.s[d])) # Randomly selection of 2 EAs from each small area & sorted
      EA.sample<-c(EA.sample,id.EA.sample)
    }
    
    ID.sample<-NULL
    for (a in 1:length(EA.sample)){
      if (length(N.c.s)==1) ID.s<-sort(sample(ID.H[ID.C==EA.sample[a]],N.c.s))
      if (length(N.c.s)>1)  ID.s<-sort(sample(ID.H[ID.C==EA.sample[a]],N.c.s[a]))
      
      if (length(N.c.s)==1 & het.func=="f4b")  ID.s<-sort(sample(ID.H[ID.C==EA.sample[a] & z.ch==0],N.c.s))
      if (length(N.c.s)>1 & het.func=="f4b")  ID.s<-sort(sample(ID.H[ID.C==EA.sample[a] & z.ch==0],N.c.s[a]))
      
      ID.sample<-c(ID.sample,ID.s)
    }
    
    data1.s<-data.1[ID.sample,]
    n<-length(data1.s$y)
    n.c<-tapply(data1.s$ID.H,data1.s$ID.C,length)
    number.cluster.s<-length(unique(data1.s$ID.C))
    ID.cluster.s<-unique(data1.s$ID.C)
    
    lm1<-lm(y~x1+x2,data1.s) # Fit the OLS model
    data1.s$uch.1<-resid(lm1)
    eta.1<-as.vector(tapply(data1.s$uch.1,data1.s$ID.C,mean))
    data1.s$eps.1<-data1.s$uch.1-rep(eta.1,n.c)
    data1.s$y.hat<-fitted.values(lm1)
    
    # Estimation of variance  component at level 2 assumong homo.. and hete.. at level one
    sig2.HM.1<-Var.Com.MM.2(data1.s$ID.C,data1.s$ID.H,eta.1,data1.s$uch.1)   # Homoskedasticity at individual level
    sig2.HT.1<-Var.Com.MM.2.H(data1.s$ID.C,data1.s$ID.H,eta.1,data1.s$eps.1) # Heteroskedasticity at individual level
    sig2.HT.1$sigma2.1<-(summary(lm1)$sigma)^2-sig2.HT.1$sigma2.2
    
    # Explanatory variables for Census and sample observations
    X.s<-cbind(data1.s$x1,data1.s$x2)
    X.U<-cbind(data.1$x1,data.1$x2)
    
    # Residual Variance estimates at level one ==================================================================== 
    
    # Estimation based on LOESS estimates (Degree 1) 
    
    if (het.est.method=="LPR") {
      
      data.1$y.hat<-cbind(rep(1,dim(X.U)[1]),X.U)%*%coef(lm1)
      loess.fit.initial<-fANCOVA::loess.as(data1.s$y.hat, data1.s$eps.1^2, degree = 1, criterion = c("gcv"), family = c("gaussian"))
      band.width.loess<-loess.fit.initial$par$span
      
      sigma2.loess<-loess(eps.1^2~y.hat, data=data1.s,span=band.width.loess,family = "gaussian",method = c("loess"),
                          control = loess.control(surface = "interpolate"),degree=1,model = TRUE)
      
      #sigma2.loess.1 <- loess(eps.1^2~x, data=data1.s,span=band.width.loess,family = "gaussian",method = c("loess"),
      #                        control = loess.control(surface = "direct"),degree=1,model = TRUE)
      
      sigma2.x.s.loess<-predict(sigma2.loess, data.frame(y.hat=data1.s$y.hat), se = FALSE)
      sigma2.x.U.loess<-predict(sigma2.loess, data.frame(y.hat=data.1$y.hat), se = FALSE)
      
      sigma2.x.U.min<-predict(sigma2.loess, data.frame(y.hat=min(data1.s$y.hat)), se = FALSE)
      sigma2.x.U.max<-predict(sigma2.loess, data.frame(y.hat=max(data1.s$y.hat)), se = FALSE)
      
      # Estimated results for individuals: LOESS
      data1.s$sig2.ch.hat.2<-sigma2.x.s.loess
      
      data.1$sig2.ch.hat.2<-sigma2.x.U.loess
      data.1$sig2.ch.hat.2[data.1$y.hat<min(data1.s$y.hat)]<-sigma2.x.U.min
      data.1$sig2.ch.hat.2[data.1$y.hat>max(data1.s$y.hat)]<-sigma2.x.U.max
      
    }
    
    
    # estimates based on Stratification method
    
    if (het.est.method=="STR") {
      
      results.IGLS<-RES.VAR.STRATA.IGLS(data1.s$y,cbind(data1.s$x1,data1.s$x2),data1.s$ID.C,data1.s$ID.H,cbind(data.1$x1,data.1$x2),data.1$ID.C,data.1$ID.H,strata.quantiles,Iteration.no=100,tol=1e-20)
      
      data1.s$sig2.ch.hat.2<-results.IGLS$sig2.ch.hat.s
      data.1$sig2.ch.hat.2<-results.IGLS$sig2.ch.hat.U
      
    }
    
    # Store the Variance components
    
    Sigma.HM[s,]<-c(sig2.HM.1$sigma2.2,sig2.HM.1$sigma2.1)
    Sigma.HT[s,]<-c(sig2.HT.1$sigma2.2,((summary(lm1)$sigma)^2-sig2.HT.1$sigma2.2))
    if (het.est.method=="STR") Sigma.HT.IGLS[s,]<-c(results.IGLS$sigma2.2.HT.IGLS,((summary(lm1)$sigma)^2-results.IGLS$sigma2.2.HT.IGLS))
    
    sigma2.ch.s[,s]<-data1.s$sig2.ch # True 
    if (het.est.method=="LPR") sigma2.ch.s.2[,s]<-data1.s$sig2.ch.hat.2 # LOESS Smooth function
    if (het.est.method=="STR") sigma2.ch.s.2[,s]<-data1.s$sig2.ch.hat.2 # Stratified Smooth Method
    
    sigma2.ch.U[,s]<-data.1$sig2.ch # True 
    if (het.est.method=="LPR") sigma2.ch.U.2[,s]<-data.1$sig2.ch.hat.2 # LOESS Smooth function
    if (het.est.method=="STR") sigma2.ch.U.2[,s]<-data.1$sig2.ch.hat.2 # Stratified Smooth Method
    
    # Generalized least square estimates of the regression parameters
    
    X.ols<-cbind(rep(1,n),cbind(data1.s$x1,data1.s$x2))
    
    # FGT estimation using CD method: MC Simulation Approach with HT estimates using LOESS method
    
    if (skedasticity=="Homoskedastic" & Bootstrap=="MC"){
      
      # Homoskedastic variance components
      
      gls.estimate<-GLS.EST(n.c,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c)


      if (length(t)==1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {      
          F11.True<-CD.MC.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        } 
      }
      
      if (length(t)>1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-CD.MC.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      } 
      
    } # CD.MC.HM.FGT.Scale with LPR end

    if (skedasticity=="Heteroskedastic" & Bootstrap=="MC" & het.est.method=="LPR"){
      
      # Heteroskedastic variance components
      
      gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c)
      
      if (length(t)==1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-CD.MC.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data1.s$sig2.ch.hat.2,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        } 
      }
      
      if (length(t)>1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-CD.MC.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data1.s$sig2.ch.hat.2,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      } 
      
    } # CD.MC.HT.FGT.Scale with LPR end
    
    if (skedasticity=="Heteroskedastic" & Bootstrap=="MC" & het.est.method=="STR"){
      
      gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c) 
      
      if (length(t)==1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          
          F11.True<-CD.MC.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data1.s$sig2.ch.hat.2,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      }
      
      if (length(t)>1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-CD.MC.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data1.s$sig2.ch.hat.2,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      } 
      
    } # CD.MC.HT.Scale with STR end
    
    # FGT estimation using CD method: Smearing Approach with HT estimates using Stratification method

    if (skedasticity=="Homoskedastic" & Bootstrap=="SM" & residual.1=="Fixed"){
      
      gls.estimate<-GLS.EST(n.c,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c)
      
      if (length(t)==1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {      
          F11.True<-CD.SM.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1="Fixed")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)    
        }
      }
      
      if (length(t)>1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-CD.SM.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1="Fixed")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      } 
      
    } # CD.SM.HM.FGT.Scale with LPR end
    
    if (skedasticity=="Homoskedastic" & Bootstrap=="SM" & residual.1=="Random"){
      
      gls.estimate<-GLS.EST(n.c,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c)
      
      if (length(t)==1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {      
          F11.True<-CD.SM.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1="Random")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)    
        }
      }
      
      if (length(t)>1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-CD.SM.HM(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,sig2.HM.1$sigma2.1,sig2.HM.1$sigma2.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1="Random")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      } 
      
    } # CD.SM.HM.FGT.Scale with Random Level one Residual

    if (skedasticity=="Heteroskedastic" & Bootstrap=="SM" & het.est.method=="LPR" & residual.1=="Fixed"){
      
      # Heteroskedastic variance components
      
      gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c)
      
      if (length(t)==1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {      
          F11.True<-CD.SM.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1="Fixed")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)    
        }
      }
      
      if (length(t)>1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-CD.SM.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1="Fixed")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      } 
      
    } # CD.SM.HT.FGT.Scale with LPR end
    
    if (skedasticity=="Heteroskedastic" & Bootstrap=="SM" & het.est.method=="LPR" & residual.1=="Random"){
      
      # Heteroskedastic variance components
      
      gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c)
      
      if (length(t)==1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {      
          F11.True<-CD.SM.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1="Random")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)    
        }
      }
      
      if (length(t)>1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-CD.SM.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1="Random")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      } 
      
    } # CD.SM.HT.FGT.Scale with LPR end
    
    if (skedasticity=="Heteroskedastic" & Bootstrap=="SM" & het.est.method=="STR" & residual.1=="Fixed"){
      
      # Heteroskedastic variance components
      
      gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c)
      
      if (length(t)==1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-CD.SM.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1="Fixed")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      }
      
      if (length(t)>1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-CD.SM.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1="Fixed")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      } 
      
    } # CD.SM.HT.Scale with STR end
    
    if (skedasticity=="Heteroskedastic" & Bootstrap=="SM" & het.est.method=="STR" & residual.1=="Random"){
      
      # Heteroskedastic variance components
      
      gls.estimate<-GLS.EST(n.c,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,X.ols,data1.s$y)
      beta.gls <- gls.estimate$beta.gls
      var.beta.gls<- gls.estimate$vcov.beta.gls
      
      # Generalized Least squares residuals
      
      data1.s$y.hat.gls<-X.ols%*%beta.gls
      data1.s$uch.1.gls<-data1.s$y-data1.s$y.hat.gls
      eta.1.gls<-as.vector(tapply(data1.s$uch.1.gls,data1.s$ID.C,mean))
      data1.s$eps.1.gls<-data1.s$uch.1.gls-rep(eta.1.gls,n.c)
      
      if (length(t)==1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
          F11.True<-CD.SM.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1="Random")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      }
      
      if (length(t)>1){
        
        r.FGT <- foreach(icount(No.Boot), .combine=f2.array) %dopar% {
          F11.True<-CD.SM.HT(beta.gls,var.beta.gls,eta.1.gls,data1.s$eps.1.gls,data1.s$sig2.ch.hat.2,sig2.HT.1$sigma2.2,sig2.HT.1$sigma2.1,data.1$sig2.ch.hat.2,data.1$ID.D,data.1$ID.C,X.U,t,parameter="FGT",residual.1="Random")
          F11.FGT0<-F11.True$F00; F11.FGT1<-F11.True$F11; F11.FGT2<-F11.True$F22
          F11.True<-NULL
          list(F11.FGT0=F11.FGT0,F11.FGT1=F11.FGT1,F11.FGT2=F11.FGT2)
        }
      } 
      
    } # CD.SM.HT.Scale with STR end
    
    if (length(t)==1){
      
      F0.True[s,]<-tapply(exp(data.1$y),data.1$ID.D,function (x) FGT.alpha(x,t,0)) # True estimates: FGT 0
      F1.True[s,]<-tapply(exp(data.1$y),data.1$ID.D,function (x) FGT.alpha(x,t,1)) # True estimates: FGT 1
      F2.True[s,]<-tapply(exp(data.1$y),data.1$ID.D,function (x) FGT.alpha(x,t,2)) # True estimates: FGT 2
      
      F0.F11[s,]<-colMeans(r.FGT$F11.FGT0) ; F0.F11.MSE[s,]<-apply(r.FGT$F11.FGT0,2,sd)
      F0.F11.Q.02.5<-apply(r.FGT$F11.FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
      F0.F11.Q.97.5<-apply(r.FGT$F11.FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
      F0.CR.I[s,]<-(F0.True[s,]>=F0.F11.Q.02.5 & F0.True[s,]<=F0.F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      
      F1.F11[s,]<-colMeans(r.FGT$F11.FGT1) ; F1.F11.MSE[s,]<-apply(r.FGT$F11.FGT1,2,sd)
      F1.F11.Q.02.5<-apply(r.FGT$F11.FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
      F1.F11.Q.97.5<-apply(r.FGT$F11.FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
      F1.CR.I[s,]<-(F1.True[s,]>=F1.F11.Q.02.5 & F1.True[s,]<=F1.F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      
      F2.F11[s,]<-colMeans(r.FGT$F11.FGT2) ; F2.F11.MSE[s,]<-apply(r.FGT$F11.FGT2,2,sd)
      F2.F11.Q.02.5<-apply(r.FGT$F11.FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
      F2.F11.Q.97.5<-apply(r.FGT$F11.FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
      F2.CR.I[s,]<-(F2.True[s,]>=F2.F11.Q.02.5 & F2.True[s,]<=F2.F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      
    }
    
    if (length(t)>1){
      
      F0.True[s,,]<-array(matrix(simplify2array(tapply(exp(data.1$y),data.1$ID.D,function (x) FGT.alpha(x,t,0))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t))) # True estimates: FGT 0
      F1.True[s,,]<-array(matrix(simplify2array(tapply(exp(data.1$y),data.1$ID.D,function (x) FGT.alpha(x,t,1))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t))) # True estimates: FGT 1
      F2.True[s,,]<-array(matrix(simplify2array(tapply(exp(data.1$y),data.1$ID.D,function (x) FGT.alpha(x,t,2))),nrow=No.Area,ncol=length(t),byrow=TRUE),dim=c(1,No.Area,length(t))) # True estimates: FGT 2
      
      F0.F11[s,,]<-colMeans(r.FGT$F11.FGT0,dims=1) ; F0.F11.MSE[s,,]<-apply(r.FGT$F11.FGT0,c(2,3),sd)        
      F0.F11.Q.02.5<-apply(r.FGT$F11.FGT0,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
      F0.F11.Q.97.5<-apply(r.FGT$F11.FGT0,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
      F0.CR.I[s,,]<-(F0.True[s,,]>=F0.F11.Q.02.5 & F0.True[s,,]<=F0.F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      
      F1.F11[s,,]<-colMeans(r.FGT$F11.FGT1,dims=1) ; F1.F11.MSE[s,,]<-apply(r.FGT$F11.FGT1,c(2,3),sd)
      F1.F11.Q.02.5<-apply(r.FGT$F11.FGT1,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
      F1.F11.Q.97.5<-apply(r.FGT$F11.FGT1,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
      F1.CR.I[s,,]<-(F1.True[s,,]>=F1.F11.Q.02.5 & F1.True[s,,]<=F1.F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      
      F2.F11[s,,]<-colMeans(r.FGT$F11.FGT2,dims=1) ; F2.F11.MSE[s,,]<-apply(r.FGT$F11.FGT2,c(2,3),sd)
      F2.F11.Q.02.5<-apply(r.FGT$F11.FGT2,c(2,3),function(x) quantile(x,0.025,na.rm=TRUE))
      F2.F11.Q.97.5<-apply(r.FGT$F11.FGT2,c(2,3),function(x) quantile(x,0.975,na.rm=TRUE))
      F2.CR.I[s,,]<-(F2.True[s,,]>=F2.F11.Q.02.5 & F2.True[s,,]<=F2.F11.Q.97.5)*1 # Converting the logical matrix into numerical matrix
      
    } 
    
  } # Simulation End
  
  list(Sigma.HM=Sigma.HM,Sigma.HT=Sigma.HT,Sigma.HT.IGLS=Sigma.HT.IGLS,#sigma2.ch.U=sigma2.ch.U,sigma2.ch.U.STR=sigma2.ch.U.2,
       F0.True=F0.True,F1.True=F1.True,F2.True=F2.True,
       F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.CR.I=F0.CR.I,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.CR.I=F1.CR.I,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.CR.I=F2.CR.I)
  
} # Function End
# ------------------------------------------------------------------------------
# Population Structure and Heteroskedasticity function : Type-I simulation
# ------------------------------------------------------------------------------
# 2nd level variance component
sig2.eta<-23.5
# Heteroskedasticity Function for 1st level residual variance
sig2.ch.1<-function(x) 94.05 # Homoskedastic : Constant on X 
sig2.ch.2<-function(x) 90+(0.75*exp(0.05*(x)))^2    # Non-Linear on X
sig2.ch.3<-function(x) 90+0.5*x^2 # Non-Linear on X
# Clusters have some unique characterisrics to vary the variance function
# Two types of households are considered: Type 1 follows sig2.ch.1 and type 2 follows sig2.ch.2
sig2.ch.4<-function(x1,x2) ifelse (x2==1, sig2.ch.2(x1), sig2.ch.3(x1))

D<-50
C.d<-10
# C.d<-c(5:9)

set.seed(1000)
if (length(D*C.d)==1) {
  N.Cluster<-round(runif(D*C.d,100,120) )
  ID.d<-rep(1:D,rep(C.d,D))
}
if (length(D*C.d)>1) {
  N.Cluster<-round(runif(sum(D*C.d),100,120) )
  ID.d<-rep(1:D,D*C.d)
}
N.Area<-as.vector(tapply(N.Cluster,ID.d,sum))
C=length(N.Cluster)
# Probabilities of being in Grop 1
set.seed(1000)
pr.c<-runif(C,0.20,0.40) # Clusterspecific probability of being Group 1
Prob.C<-rep(pr.c,N.Cluster) 
# ------------------------------------------------------------------------------
# Sample Structure 
# ------------------------------------------------------------------------------
C.d.s=2 # Number of cluster per small area in  sample 
# C.d.s=c(2,1,3,2,2)
set.seed(1000)
if (length(D*C.d.s)==1) {
  N.c.s<-round(runif(D*C.d.s,10,20) )
}
if (length(D*C.d.s)>1) {
  N.c.s<-round(runif(sum(D*C.d.s),10,20) )
}
quant=c(0.10,0.25,0.5,0.75,0.90) # Quantiles 
strata.quantiles<-seq(0,100,10)
# ------------------------------------------------------------------------------
# Check the functions for Simulation Study: Type I - Mean and DF
# ------------------------------------------------------------------------------
set.seed(2015)
Scenario.i.ELL.HM.PB.Mean<-Simulation.ELL.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Homoskedastic"),Bootstrap=c("PB"),residual.1=c("unconditional"),parameter="MEAN",quant,No.Boot=5,No.Sim=5)
Scenario.i.ELL.HM.PB.DF<-Simulation.ELL.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Homoskedastic"),Bootstrap=c("PB"),residual.1=c("unconditional"),parameter="DF",quant,No.Boot=5,No.Sim=5)
Scenario.i.ELL.HT.PB.Mean<-Simulation.ELL.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f2"),skedasticity=c("Heteroskedastic"),Bootstrap=c("PB"),residual.1=c("unconditional"),parameter="MEAN",quant,No.Boot=5,No.Sim=5)
Scenario.i.ELL.HT.PB.DF<-Simulation.ELL.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f2"),skedasticity=c("Heteroskedastic"),Bootstrap=c("PB"),residual.1=c("unconditional"),parameter="DF",quant,No.Boot=5,No.Sim=5)
# Unconditional NPB
Scenario.i.ELL.HM.NPB.Mean<-Simulation.ELL.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f3"),skedasticity=c("Homoskedastic"),Bootstrap=c("NPB"),residual.1=c("unconditional"),parameter="MEAN",quant,No.Boot=5,No.Sim=5)
Scenario.i.ELL.HM.NPB.DF<-Simulation.ELL.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f3"),skedasticity=c("Homoskedastic"),Bootstrap=c("NPB"),residual.1=c("unconditional"),parameter="DF",quant,No.Boot=5,No.Sim=5)
Scenario.i.ELL.HT.NPB.Mean<-Simulation.ELL.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f4"),skedasticity=c("Heteroskedastic"),Bootstrap=c("NPB"),residual.1=c("unconditional"),parameter="MEAN",quant,No.Boot=5,No.Sim=5)
Scenario.i.ELL.HT.NPB.DF<-Simulation.ELL.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f4"),skedasticity=c("Heteroskedastic"),Bootstrap=c("NPB"),residual.1=c("unconditional"),parameter="DF",quant,No.Boot=5,No.Sim=5)
# Conditional NPB
Scenario.i.ELL.HM.NPB.Mean.Cond<-Simulation.ELL.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f4b"),skedasticity=c("Homoskedastic"),Bootstrap=c("NPB"),residual.1=c("conditional"),parameter="MEAN",quant,No.Boot=5,No.Sim=5)
Scenario.i.ELL.HM.NPB.DF.Cond<-Simulation.ELL.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f4b"),skedasticity=c("Homoskedastic"),Bootstrap=c("NPB"),residual.1=c("conditional"),parameter="DF",quant,No.Boot=5,No.Sim=5)
Scenario.i.ELL.HT.NPB.Mean.Cond<-Simulation.ELL.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Heteroskedastic"),Bootstrap=c("NPB"),residual.1=c("conditional"),parameter="MEAN",quant,No.Boot=5,No.Sim=5)
Scenario.i.ELL.HT.NPB.DF.Cond<-Simulation.ELL.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Heteroskedastic"),Bootstrap=c("NPB"),residual.1=c("conditional"),parameter="DF",quant,No.Boot=5,No.Sim=5)
# ------------------------------------------------------------------------------
# Simulation Study: Type-I - Mean & DF : CDMC Methods
# ------------------------------------------------------------------------------
set.seed(2015)
Scenario.1.CD.HM.MC.Mean<-Simulation.CD.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Homoskedastic"),Bootstrap=c("MC"),residual.1=c("Fixed"),het.est.method=c("STR"),strata.quantiles,quant,parameter=c("MEAN"),No.Boot=5,No.Sim=5)
Scenario.1.CD.HM.MC.DF<-Simulation.CD.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Homoskedastic"),Bootstrap=c("MC"),residual.1=c("Fixed"),het.est.method=c("STR"),strata.quantiles,quant,parameter=c("DF"),No.Boot=5,No.Sim=5)
Scenario.1.CD.HT.MC.Mean<-Simulation.CD.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Heteroskedastic"),Bootstrap=c("MC"),residual.1=c("Fixed"),het.est.method=c("STR"),strata.quantiles,quant,parameter=c("MEAN"),No.Boot=5,No.Sim=5)
Scenario.1.CD.HT.MC.DF<-Simulation.CD.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Heteroskedastic"),Bootstrap=c("MC"),residual.1=c("Fixed"),het.est.method=c("STR"),strata.quantiles,quant,parameter=c("DF"),No.Boot=5,No.Sim=5)
# ------------------------------------------------------------------------------
# Simulation Study: Type-I - Mean & DF : CDSM Methods
# ------------------------------------------------------------------------------
Scenario.1.CD.HM.SM.Fixed.Mean<-Simulation.CD.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Homoskedastic"),Bootstrap=c("SM"),residual.1=c("Fixed"),het.est.method=c("STR"),strata.quantiles,quant,parameter=c("MEAN"),No.Boot=5,No.Sim=5)
Scenario.1.CD.HM.SM.Random.Mean<-Simulation.CD.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Homoskedastic"),Bootstrap=c("SM"),residual.1=c("Random"),het.est.method=c("STR"),strata.quantiles,quant,parameter=c("MEAN"),No.Boot=5,No.Sim=5)
Scenario.1.CD.HM.SM.Fixed.DF<-Simulation.CD.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Homoskedastic"),Bootstrap=c("SM"),residual.1=c("Fixed"),het.est.method=c("STR"),strata.quantiles,quant,parameter=c("DF"),No.Boot=5,No.Sim=5)
Scenario.1.CD.HM.SM.Random.DF<-Simulation.CD.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Homoskedastic"),Bootstrap=c("SM"),residual.1=c("Random"),het.est.method=c("STR"),strata.quantiles,quant,parameter=c("DF"),No.Boot=5,No.Sim=5)

Scenario.1.CD.HT.SM.Fixed.Mean<-Simulation.CD.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Heteroskedastic"),Bootstrap=c("SM"),residual.1=c("Fixed"),het.est.method=c("STR"),strata.quantiles,quant,parameter=c("MEAN"),No.Boot=5,No.Sim=5)
Scenario.1.CD.HT.SM.Random.Mean<-Simulation.CD.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Heteroskedastic"),Bootstrap=c("SM"),residual.1=c("Random"),het.est.method=c("STR"),strata.quantiles,quant,parameter=c("MEAN"),No.Boot=5,No.Sim=5)
Scenario.1.CD.HT.SM.Fixed.DF<-Simulation.CD.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Heteroskedastic"),Bootstrap=c("SM"),residual.1=c("Fixed"),het.est.method=c("STR"),strata.quantiles,quant,parameter=c("DF"),No.Boot=5,No.Sim=5)
Scenario.1.CD.HT.SM.Random.DF<-Simulation.CD.SADF(N.Area,N.Cluster,C.d.s,N.c.s,df=20,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Heteroskedastic"),Bootstrap=c("SM"),residual.1=c("Random"),het.est.method=c("STR"),strata.quantiles,quant,parameter=c("DF"),No.Boot=5,No.Sim=5)
# ------------------------------------------------------------------------------
# Population Structure and Heteroskedasticity function : Type-II simulation
# ------------------------------------------------------------------------------
# 2nd level variance component
sig2.eta<-0.05
# Heteroskedasticity Function for 1st level residual variance =====
# Application of the heteroskedasticity function of 1st level residual variance in Poverty data set
sig2.ch.1<-function(x) 0.20 # Homoskedastic : Constant on X 
sig2.ch.2<-function(x) 0.19+0.005*exp(0.05*x^2)
sig2.ch.3<-function(x) 0.20+0.015*((x-mean(x))/sd(x))^2
# Clusters have some unique characterisrics to vary the variance function
# Two types of households are considered: Type 1 follows sig2.ch.1 and type 2 follows sig2.ch.2
sig2.ch.4<-function(x1,x2) ifelse (x2==1, sig2.ch.2(x1), sig2.ch.3(x1))
D<-50
C.d<-10
# C.d<-c(5:9)
set.seed(1000)
if (length(D*C.d)==1) {
  N.Cluster<-round(runif(D*C.d,100,120) )
  ID.d<-rep(1:D,rep(C.d,D))
}
if (length(D*C.d)>1) {
  N.Cluster<-round(runif(sum(D*C.d),100,120) )
  ID.d<-rep(1:D,D*C.d)
}
N.Area<-as.vector(tapply(N.Cluster,ID.d,sum))
C=length(N.Cluster)
# Probabilities of being in Grop 1
set.seed(1000)
pr.c<-runif(C,0.20,0.40) # Clusterspecific probability of being Group 1
Prob.C<-rep(pr.c,N.Cluster) 
# ------------------------------------------------------------------------------
# Sample Structure 
# ------------------------------------------------------------------------------
C.d.s=2 # Number of cluster per small area in  sample 
# C.d.s=c(2,1,3,2,2)
set.seed(1000)
if (length(D*C.d.s)==1) {
  N.c.s<-round(runif(D*C.d.s,10,20) )
}
if (length(D*C.d.s)>1) {
  N.c.s<-round(runif(sum(D*C.d.s),10,20) )
}
N<-sum(N.Area)
C<-length(N.Cluster)
quant=c(0.10,0.25)
strata.quantiles<-seq(0,100,10)
# quant=c(0.25)
# ------------------------------------------------------------------------------
# Generating explanatory variables
# ------------------------------------------------------------------------------
Sigma.Mu<-c(0.5,0.75)
Sigma2.X<-matrix(c(1.50,0.10,0.10,0.95),2,2,byrow=TRUE)
X<-rmvnorm(N,Sigma.Mu,Sigma2.X)
beta<-c(6,0.5,-0.55)
# ------------------------------------------------------------------------------
# Simulation Study: Type-II - FGT : ELL Methods
# ------------------------------------------------------------------------------
Simulation.ELL.FGT(N.Area,N.Cluster,C.d.s,N.c.s,beta,Sigma.Mu,Sigma2.X,sig2.eta,Prob.C,het.func=c("f1","f2","f3","f4","f4b"),
                             skedasticity=c("Homoskedastic","Heteroskedastic"),Bootstrap=c("PB","NPB"),residual.1=c("unconditional","conditional"),quant,parameter=c("FGT"),No.Boot,No.Sim)
set.seed(2015)
Scenario.1.ELL.HM.PB.FGT.UNC<-Simulation.ELL.FGT(N.Area,N.Cluster,C.d.s,N.c.s,beta,Sigma.Mu,Sigma2.X,sig2.eta,Prob.C,het.func=c("f1"),
                                             skedasticity=c("Homoskedastic"),Bootstrap=c("PB"),residual.1=c("unconditional"),quant,parameter=c("FGT"),No.Boot=5,No.Sim=5)
# Unconditional NPB
Scenario.1.ELL.HM.NPB.FGT<-Simulation.ELL.FGT(N.Area,N.Cluster,C.d.s,N.c.s,beta,Sigma.Mu,Sigma2.X,sig2.eta,Prob.C,het.func=c("f1"),
                                             skedasticity=c("Homoskedastic"),Bootstrap=c("NPB"),residual.1=c("unconditional"),quant,parameter=c("FGT"),No.Boot=5,No.Sim=5)
# Conditional NPB
Scenario.1.ELL.HM.NPB.FGT<-Simulation.ELL.FGT(N.Area,N.Cluster,C.d.s,N.c.s,beta,Sigma.Mu,Sigma2.X,sig2.eta,Prob.C,het.func=c("f1"),
                                              skedasticity=c("Homoskedastic"),Bootstrap=c("NPB"),residual.1=c("conditional"),quant,parameter=c("FGT"),No.Boot=5,No.Sim=5)
# ------------------------------------------------------------------------------
# Function for Simulation Study: Type-II - FGT : CDSM Methods
# ------------------------------------------------------------------------------
set.seed(2015)
Scenario.1.CD.HM.SM.FGT.Fixed<-Simulation.CD.FGT(N.Area,N.Cluster,C.d.s,N.c.s,beta,Sigma.Mu,Sigma2.X,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Homoskedastic"),Bootstrap=c("SM"),residual.1="Fixed",het.est.method=c("STR"),strata.quantiles,quant,parameter=c("FGT"),No.Boot=5,No.Sim=5)
Scenario.1.CD.HM.SM.FGT.Random<-Simulation.CD.FGT(N.Area,N.Cluster,C.d.s,N.c.s,beta,Sigma.Mu,Sigma2.X,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Homoskedastic"),Bootstrap=c("SM"),residual.1="Random",het.est.method=c("STR"),strata.quantiles,quant,parameter=c("FGT"),No.Boot=5,No.Sim=5)
# ------------------------------------------------------------------------------
# Function for Simulation Study: Type-II - FGT : CDMC Methods
# ------------------------------------------------------------------------------
Scenario.1.CD.HM.MC.FGT<-Simulation.CD.FGT(N.Area,N.Cluster,C.d.s,N.c.s,beta,Sigma.Mu,Sigma2.X,sig2.eta,Prob.C,het.func=c("f1"),skedasticity=c("Homoskedastic"),Bootstrap=c("MC"),residual.1="Random",het.est.method=c("STR"),strata.quantiles,quant,parameter=c("FGT"),No.Boot=5,No.Sim=5)


