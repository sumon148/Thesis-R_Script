# ------------------------------------------------------------------------------
# Script 4: Chapter Six
# Subject: Application of ELL- and CD-type estimators with their modified version 
# to Bangladesh data: Census 2001 and HIES 2001
# Description: Two-level model with homoskedastic (HM) and Heteroskedastic (HT) level-one errors but HM level-two errors
# ------------------------------------------------------------------------------
rm(list=ls(all=TRUE))
# ------------------------------------------------------------------------------
# Loading Packages
# ------------------------------------------------------------------------------
library(nlme)
library(foreign)
library(MASS)
library(survey)
library(mvtnorm)
library(Matrix)
library(foreach)
library(doMC)
registerDoMC(40)
#-------------------------------------------------------------------------------
# Functions  
# ------------------------------------------------------------------------------
FGT.alpha<-function(y,z,alpha){
  t.z=ifelse(y<z,1,0)
  t.z.alpha=t.z*((rep(1,length(y))-y/z)^alpha)
  povert=sum(t.z.alpha)
  povert
}
# ------------------------------------------------------------------------------
tapply.order<-function(value,area,FUN,target.order){
  # value: The values
  # area: target area
  # target.order: The order u wish to see the outcome ....
  
  raw.output<-tapply(value,area,FUN)
  data<-data.frame(key=names(raw.output), value=raw.output)
  ordered.value<-data[match(target.order, data$key),]$value
  return(ordered.value)
}
# ------------------------------------------------------------------------------
Var.Com.MM.2<-function(level.2,level.1,res.2,res.1){
  # Homoskedasticity at both levels
  # level.2: ID number of level 2
  # level.1: ID number of level 1
  # res.2: Cluster level residuals (average of marginal residuals of respective cluster)
  # res.1: HH level residuals (Marginal residuals of HHs / OLS residuals)
  
  level.2<-as.numeric(factor(level.2))
  level.1<-as.numeric(factor(level.1))
  
  n.2<-as.vector(table(level.2))
  C<-length(n.2)
  ID.C<-unique(level.2)
  
  n<-length(level.1)
  
  n0.bar.2<-sum(n.2^2)/sum(n.2)
  s1.e<-sum((res.1-mean(res.1))^2)/(n-1)
  s2.e<-sum(n.2*(res.2-mean(res.1))^2)/(C-1)
  sigma2.2<-max(((n-1)*(C-1))/((n-n0.bar.2)*(n-C))*(-s1.e+s2.e),0)
  sigma2.1<-max((n-1)/(n-C)*s1.e-(C-1)/(n-C)*s2.e,0)
  result<-list(sigma2.1=sigma2.1,sigma2.2=sigma2.2)
  return(result)
  
}
# ------------------------------------------------------------------------------
Var.Com.MM.3<-function(level.3,level.2,level.1,res.3,res.2,res.1){
  # Homoskedasticity at all three levels
  # level.3: ID number of level 3
  # level.2: ID number of level 2
  # level.1: ID number of level 1
  # res.2: Cluster level residuals (average of marginal residuals of respective cluster)
  # res.1: HH level residuals (Marginal residuals of HHs / OLS residuals)
  
  level.3<-as.numeric(factor(level.3))
  level.2<-as.numeric(factor(level.2))
  level.1<-as.numeric(factor(level.1))
  
  n.3<-as.vector(table(level.3))
  n.2<-as.vector(table(level.2))
  n<-length(level.1)
  
  D<-length(n.3)
  C<-length(n.2)
  ID.D<-unique(level.3)
  ID.C<-unique(level.2)
  
  n0.bar.2<-sum(n.2^2)/sum(n.2)
  n0.bar.3<-sum(n.3^2)/sum(n.3)
  
  # Area wise calculation
  
  n.0i<-NULL # sum(n.2^2)/sum(n.2)
  for (d in 1:D){
    n.i.j<-tapply(level.1[level.3==d],level.2[level.3==d],length)
    n.0i<-c(n.0i,sum(n.i.j^2)/sum(n.i.j))
  }
  
  #  n.0i<-NULL # sum(n.2^2)/sum(n.2)
  #  for (d in unique(level.3)){
  #    n.i.j<-tapply(level.1[level.3==d],level.2[level.3==d],length)
  #    n.0i<-c(n.0i,sum(n.i.j^2)/sum(n.i.j))
  #  }
  
  
  sum.n.0i<-sum(n.0i)
  
  s1.e<-sum((res.1-mean(res.1))^2)/(n-1)
  s2.e<-sum(n.2*(res.2-mean(res.1))^2)/(C-1)
  s3.e<-sum(n.3*(res.3-mean(res.1))^2)/(D-1)
  
  sigma2.1<-(n-1)*s1.e/(n-C)-(C-1)*s2.e/(n-C)
  sigma2.2<-(-(n-1)*(C-D)*s1.e+(C-1)*(n-D)*s2.e-(D-1)*(n-C)*s3.e)/((n-sum.n.0i)*(n-C))
  sigma2.3<-((n-1)*((C-1)*(sum.n.0i-n0.bar.2)-(D-1)*(n-n0.bar.2))*s1.e+
               (C-1)*((D-1)*(n-n0.bar.2)-(n-1)*(sum.n.0i-n0.bar.2))*s2.e+
               (D-1)*(n-n0.bar.2)*(n-C)*s3.e)/((n-n0.bar.3)*(n-sum.n.0i)*(n-C))
  
  
  result<-list(sigma2.1=sigma2.1,sigma2.2=sigma2.2,sigma2.3=sigma2.3)
  return(result)
  
}
# ------------------------------------------------------------------------------
Var.Com.MM.2.H<-function(level.2,level.1,res.2,con.res.1){
  # Heteroskedasticity at 1st level
  # Homoskedasticity at 2nd level
  # level.2: ID number of level 2
  # level.1: ID number of level 1
  # res.2: Cluster level residuals (average of marginal residuals of respective cluster)
  # con.res.1: HH level conditional residuals (Marginal residuals of HHs - Cluster level residuals)
  
  
  n.2<-as.vector(table(level.2))
  n.1<-length(level.1)
  
  C<-length(n.2)
  ID.C<-unique(level.2)
  
  wc<-n.2/sum(n.2)
  tau.2.c<-tapply(con.res.1,level.2,var)/n.2
  sigma2.2<-max((sum(wc*(res.2-mean(res.2))^2)-sum(wc*(1-wc)*tau.2.c))/sum(wc*(1-wc)),0)
  
  
  result<-list(sigma2.2=sigma2.2)
  return(result)
  
}
# ------------------------------------------------------------------------------
Var.Com.MM.3.H<-function(level.3,level.2,level.1,res.3,res.2,con.res.1){
  # Heteroskedasticity at 1st level
  # Homoskedasticity at 2nd and 3rd level
  # level.3  : ID of level 3
  # level.2  : ID of level 2
  # level.1  : ID of level 1
  # ID will be in ascending orders
  #   res.3  : Area level residuals (average of marginal residuals of respective area)
  #   res.2  : Cluster level residuals (average of marginal residuals of respective cluster)
  # con.res.1: HH level conditional residuals (Marginal residuals of HHs - Cluster level residuals - Area level residuals)
  
  level.3<-as.numeric(factor(level.3))
  level.2<-as.numeric(factor(level.2))
  level.1<-as.numeric(factor(level.1))
  
  n.3<-as.vector(table(level.3))
  n.2<-as.vector(table(level.2))
  n.1<-length(level.1)
  
  D<-length(n.3)
  C<-length(n.2)
  ID.D<-unique(level.3)
  ID.C<-unique(level.2)
  
  # Number of cluster per area
  n.2.3<-NULL
  for (d in 1: D) n.2.3<-c(n.2.3,length(unique(level.2[level.3==d])))
  ID.C.D<-rep(ID.D,n.2.3)
  
  
  #  n0.bar.2<-sum(n.2^2)/sum(n.2)
  #  n0.bar.3<-sum(n.3^2)/sum(n.3)
  
  # Area wise calculation
  
  #  n.0i<-NULL # sum(n.2^2)/sum(n.2)
  #  for (d in 1:D){
  #    n.i.j<-tapply(level.1[level.3==d],level.2[level.3==d],length)
  #    n.0i<-c(n.0i,sum(n.i.j^2)/sum(n.i.j))
  #  }
  # sum.n.0i<-sum(n.0i)
  
  
  
  #  s1.e<-sum((res.1-mean(res.1))^2)/(n-1)
  #  s2.e<-sum(n.2*(res.2-mean(res.1))^2)/(C-1)
  #  s3.e<-sum(n.3*(res.3-mean(res.1))^2)/(D-1)
  
  tau.2.c<-tapply(con.res.1,level.2,var)/n.2
  tau.2.d<-tapply(n.2^2*tau.2.c,ID.C.D,sum)/n.3^2
  wc<-n.2/sum(n.2)
  wd<-n.3/sum(n.3)
  
  
  sigma2.2<-max( ( sum(wc*(res.2-mean(res.2))^2) - sum(wd*(res.3-mean(res.3))^2) - sum(wc*(1-wc)*tau.2.c) + sum(wd*(1-wd)*tau.2.d) ) /
                   (sum(wc) - sum (1/wd*tapply(wc^2,ID.C.D,sum)))  , 0)
  
  sigma2.3<-max(
    ( sum( (1/wd-1)*tapply(wc^2,ID.C.D,sum) ) * sum(wc*(1-wc)*tau.2.c)
      - sum(wc*(1-wc)) * sum(wd*(1-wd)*tau.2.d)
      - sum( (1/wd-1)*tapply(wc^2,ID.C.D,sum) ) * sum(wc*(res.2-mean(res.2))^2)
      + sum(wc*(1-wc)) * sum(wd*(res.3-mean(res.3))^2) )  /
      ( sum(wd*(1-wd)) * (sum(wc) - sum (1/wd*tapply(wc^2,ID.C.D,sum))) )
  )
  
  
  result<-list(sigma2.2=sigma2.2,sigma2.3=sigma2.3)
  return(result)
  
}
# ------------------------------------------------------------------------------
GLS.EST.2L<-function(level.2,level.1,sigma2.2,sigma2.1,x.matrix,y.s){
  # level.2: Cluster Level ID
  # level.1: HH Level ID
  # sigma2.2, sigma2.1 level specific VC (Homoskedastic here)
  # Output: beta estimates with thier variance covariance matrix
  # sigma2.1: May be homoskedastic or heteroskedastic
  
  level.2<-as.numeric(factor(level.2))
  level.1<-as.numeric(factor(level.1))
  
  n.2<-as.vector(table(level.2))
  n<-sum(n.2)
  number.cluster.s<-length(n.2)
  
  if (length(sigma2.1)==1){
    sampleList <- list()
    for (i in 1:number.cluster.s) sampleList[[i]]<-diag(rep(sigma2.1,n.2[i]))+sigma2.2*matrix(1,n.2[i],n.2[i])
  }
  
  
  if (length(sigma2.1)>1){
    sampleList <- list()
    j<-1
    for (i in 1:number.cluster.s) {
      sampleList[[i]]<-diag(sigma2.1[j:(j+n.2[i]-1)])+sigma2.2*matrix(1,n.2[i],n.2[i])
      j<-j+n.2[i]
    }
  }
  
  V<-bdiag(sampleList)
  inv.V<-solve(V,sparse=TRUE)
  xtx<-(t(x.matrix)%*%inv.V%*%(x.matrix))
  xty<-(t(x.matrix)%*%inv.V%*%(y.s))
  beta.gls <- solve(xtx)%*%xty
  vcov.beta.gls<- solve(t(x.matrix)%*%(x.matrix)) %*% (t(x.matrix)%*%V%*%(x.matrix)) %*% solve(t(x.matrix)%*%(x.matrix))
  list(beta.gls=as.matrix(beta.gls),vcov.beta.gls=as.matrix(vcov.beta.gls),V=V)
}
# ------------------------------------------------------------------------------
GLS.EST.3L<-function(level.3,level.2,level.1,sigma2.3,sigma2.2,sigma2.1,x.matrix,y.s){
  # level.3: Area Level ID
  # level.2: Cluster Level ID
  # level.1: HH Level ID
  # sigma2.3, sigma2.2, sigma2.1 level specific VC (Homoskedastic here)
  # Output: beta estimates with thier variance covariance matrix
  # sigma2.1: May be homoskedastic or heteroskedastic
  
  library(Matrix)
  
  level.3<-as.numeric(factor(level.3))
  level.2<-as.numeric(factor(level.2))
  level.1<-as.numeric(factor(level.1))
  
  n.3<-as.vector(table(level.3))
  n.2<-as.vector(table(level.2))
  D<-length(n.3)
  
  sampleList <- list()
  
  for (d in 1:D){
    n.i.j<-tapply(level.1[level.3==d],level.2[level.3==d],length)
    n.i<-sum(n.i.j)
    
    if (length(sigma2.1)==1) {
      clusterlist<-list()
      for (i in 1:length(n.i.j)) clusterlist[[i]]<-matrix(1,n.i.j[i],n.i.j[i])
      
      sampleList[[d]]<-diag(rep(sigma2.1,n.i))+bdiag(clusterlist)*sigma2.2+sigma2.3*matrix(1,n.i,n.i)
    }
    
    if (length(sigma2.1)>1){
      clusterlist<-list()
      for (i in 1:length(n.i.j)) clusterlist[[i]]<-matrix(1,n.i.j[i],n.i.j[i])
      
      sampleList[[d]]<-diag(sigma2.1[level.1[level.3==d]])+bdiag(clusterlist)*sigma2.2+sigma2.3*matrix(1,n.i,n.i)
    }
    
  }
  
  
  V<-bdiag(sampleList)
  inv.V<-solve(V,sparse=TRUE)
  xtx<-(t(x.matrix)%*%inv.V%*%(x.matrix))
  xty<-(t(x.matrix)%*%inv.V%*%(y.s))
  beta.gls <- solve(xtx)%*%xty
  vcov.beta.gls<- solve(t(x.matrix)%*%(x.matrix)) %*% (t(x.matrix)%*%V%*%(x.matrix)) %*% solve(t(x.matrix)%*%(x.matrix))
  list(beta.gls=as.matrix(beta.gls),vcov.beta.gls=as.matrix(vcov.beta.gls),V=V)
}
# ------------------------------------------------------------------------------
GLS.EST<-function(n.c,sigma2.ch,sigma2.c,x.matrix,y.s){
  # n.c is size of clusters
  # sigma2.ch is a vector (or constant) of variance components at HH level
  # sigma2.c is variance components at cluster level
  # Output: beta estimates with thier variance covariance matrix
  # This function is used for "RES.VAR.STRATA.IGLS" function
  
  library(Matrix)
  n<-sum(n.c)
  number.cluster.s<-length(n.c)
  
  if (length(sigma2.ch)==1){
    sampleList <- list()
    for (i in 1:number.cluster.s) sampleList[[i]]<-diag(rep(sigma2.ch,n.c[i]))+sigma2.c*matrix(1,n.c[i],n.c[i])
  }
  
  if (length(sigma2.ch)>1){
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
rsquared.lmm.mom<-function(beta,Model.Matrix,est.sigma2){
  # Calculation of R-squared value: Marginal & Conditional
  # Get design matrix of fixed effects from model
  Fmat <- Model.Matrix
  # Get variance of fixed effects by multiplying coefficients by design matrix
  VarF <- var(as.vector(t(beta)%*%t(Model.Matrix)))
  # Get variance of random effects by extracting variance components
  VarRand <- sum(as.numeric(unlist(est.sigma2)[-1]), na.rm=T)
  VarResid <- as.numeric(unlist(est.sigma2)[1])
  R.squared.M<-VarF/(VarF+VarRand+VarResid)
  R.squared.C<-(VarF+VarRand)/(VarF+VarRand+VarResid)
  list(VarF=VarF,VarRand=VarRand,VarResid=VarResid,R.squared.M=R.squared.M,R.squared.C=R.squared.C)
}
# ------------------------------------------------------------------------------
RES.VAR.STRATA.IGLS.2L <- function(y.s,x.s,ID.C.s,ID.H.s,x.U,ID.C.U,ID.H.U,quantiles,Iteration.no,tol=1e-50){
  # require function "GLS.EST"
  # Residual variance estimation using stratification method based on IGLS method
  # For estimating heterskedastic residual variances based on stratification method
  # y.s,x.s,ID.C.s,ID.H.s for sample data set
  # x.s , x.U vector or Matrix
  # data set should be ordered by cluster and hh
  # quantiles : How many groups are aimed and vector of percentiles (say: c(0:10)/max(c(0:10))
  # Iteration.no: How many maximum iteration is Fixed
  # return: No. of iteration, HT residual variances for both sample and population individuals,
  # return: homoskedastic 2nd var comp., IGLS.beta, var.cov(IGLS.beta)
  # This function is used for 2-level model with HT level-one errors
  
  ID.C.s<-as.numeric(factor(ID.C.s))
  ID.H.s<-as.numeric(factor(ID.H.s))
  
  ID.C.U<-as.numeric(factor(ID.C.U))
  ID.H.U<-as.numeric(factor(ID.H.U))
  
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
  
  cut.U[1]<-min(data.U$y.fixed,na.rm=TRUE)
  cut.U[length(cut.U)]<-max(data.U$y.fixed,na.rm=TRUE)
  
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
sigma2.ch.ELL<-function(y,x.s,x.U){
  # Heteroskedasticity Modelling via ELL approach
  # y: Level one Residuls
  # x.s: Matrix of potential explanatory variables (explaining heteroskedastciity) for the Sample individuals
  # x.U: Matrix of explanatory variables for the Full Census individuals
  
  A <- 1.05*max(y^2)
  h <- log(y^2/(A-y^2))
  reg.alpha <- lm(h~x.s)
  sigma2.alpha <- sum(reg.alpha$residuals^2)/reg.alpha$df.residual
  B <- exp(reg.alpha$fitted.values)
  sig2.ch.s <- A*B/(1+B) + 0.5*sigma2.alpha*(A*B)*(1-B)/((1+B)^3)
  R.squared<-summary(reg.alpha)$r.squared
  alpha<-coef(reg.alpha)
  vcov.alpha<-vcov(reg.alpha)
  
  if (is.vector(x.U)) B.U <- exp(cbind(rep(1,length(x.U)),x.U)%*%alpha)
  if (is.matrix(x.U)) B.U <- exp(cbind(rep(1,dim(x.U)[1]),x.U)%*%alpha)
  
  sigma2.ch.U <- A*B.U/(1+B.U) + 0.5*sigma2.alpha*(A*B.U)*(1-B.U)/((1+B.U)^3)
  
  list(x.s=x.s,x.U=x.U,sigma2.ch.s=sig2.ch.s,sigma2.ch.U=sigma2.ch.U,alpha=alpha,vcov.alpha=vcov.alpha,A=A,sigma2.alpha=sigma2.alpha,R.squared=R.squared)
}
# ------------------------------------------------------------------------------
RES.VAR.STRATA.IGLS.3L <- function(y.s,x.s,ID.D.s,ID.C.s,ID.H.s,x.U,ID.D.U,ID.C.U,ID.H.U,quantiles,Iteration.no,tol=1e-50){
  # Residual variance estimation using stratification method based on IGLS method
  # For estimating heterskedastic residual variances based on stratification method
  # y.s,x.s,ID.C.s,ID.H.s for sample data set
  # x.s, x.U vector or Matrix
  # data set should be ordered by cluster and hh
  # quantiles : How many groups are aimed and vector of percentiles (say: c(0:10)/max(c(0:10))
  # Iteration.no: How many maximum iteration is Fixed
  # return: No. of iteration, HT residual variances for both sample and population individuals,
  # return: homoskedastic 2nd var comp., IGLS.beta, var.cov(IGLS.beta)
  # This function is used for 3-level model with HT level-one errors
  
  ID.D.s<-as.numeric(factor(ID.D.s))
  ID.C.s<-as.numeric(factor(ID.C.s))
  ID.H.s<-as.numeric(factor(ID.H.s))
  
  ID.D.U<-as.numeric(factor(ID.D.U))
  ID.C.U<-as.numeric(factor(ID.C.U))
  ID.H.U<-as.numeric(factor(ID.H.U))
  
  group<-quantiles/max(quantiles)
  n<-length(y.s)
  
  if (is.vector(x.s)) {
    data.s<-data.frame(y=y.s,x=x.s,ID.D=ID.D.s,ID.C=ID.C.s,ID.H=ID.H.s)
    lm.model<-lm(y~x,data=data.s)
  }
  
  if (is.matrix(x.s)) {
    data.s<-data.frame(y=y.s,ID.D=ID.D.s,ID.C=ID.C.s,ID.H=ID.H.s)
    lm.model<-lm(y.s~ x.s)
  }
  
  data.s$u.ch<-resid(lm.model)
  eta.s<-as.vector(tapply(data.s$u.ch,data.s$ID.C,mean))
  v.s<-as.vector(tapply(data.s$u.ch,data.s$ID.D,mean))
  
  n.c<-as.vector(table(data.s$ID.C))
  n.d<-as.vector(table(data.s$ID.D))
  
  data.s$eps.s<-data.s$u.ch-rep(eta.s,n.c)-rep(v.s,n.d)
  data.s$y.hat<-fitted.values(lm.model)
  
  # 2nd var com assumimg Homoskedasticity at individual level
  #sig2.HM<-Var.Com.MM.3(level.3=data.s$ID.D,level.2=data.s$ID.C,level.1=data.s$ID.H,res.3=v.s,res.2=eta.s,res.1=data.s$u.ch)
  
  # 2nd var com assumimg Heteroskedasticity at individual level
  sig2.HT<-Var.Com.MM.3.H(level.3=data.s$ID.D,level.2=data.s$ID.C,level.1=data.s$ID.H,res.3=v.s,res.2=eta.s,con.res.1=data.s$eps.s)
  
  # Creating groups on the basis of gropus quantiles
  data.s<-within(data.s, decile <- as.integer(cut(y.hat, quantile(y.hat, probs=group), include.lowest=TRUE, labels=FALSE)))
  
  # Finding group means (varaince for that group) for the constructed groups
  data.s<-within(data.s, sig2.ch.hat <- ave(eps.s^2, decile, FUN = mean))
  
  X.ols<-model.matrix(lm.model)
  
  #if (is.matrix(x.s)) X.ols<-cbind(rep(1,n), x.s)
  
  # These estimates will change over iteration
  
  x0<-data.s$sig2.ch.hat  # Initial Residual variances
  sigma2.2<-sig2.HT$sigma2.2  # Initial 2nd variance component
  sigma2.3<-sig2.HT$sigma2.3
  
  # Iterative GLS start from here
  i <- 1
  
  while (i <= Iteration.no) {
    
    gls.estimate.i<-GLS.EST.3L(data.s$ID.D,data.s$ID.C,data.s$ID.H,
                               sigma2.3,sigma2.2,x0,x.matrix=X.ols,data.s$y)
    
    
    #gls.estimate.i<-GLS.EST(n.c,x0,sigma2.2,X.ols,data.s$y)
    
    data.s$y.hat.i<-X.ols%*%gls.estimate.i$beta.gls
    data.s$u.ch.i<-data.s$y-data.s$y.hat.i
    eta.i<-as.vector(tapply(data.s$u.ch.i,data.s$ID.C,mean))
    v.i<-as.vector(tapply(data.s$u.ch.i,data.s$ID.D,mean))
    data.s$eps.i<-data.s$u.ch.i-rep(eta.i,n.c)-rep(v.i,n.d)
    
    data.s<-within(data.s, decile <- as.integer(cut(y.hat.i, quantile(y.hat.i, probs=group), include.lowest=TRUE, labels=FALSE)))
    
    # This decile will replace the initial decile estimates
    
    data.s<-within(data.s, sig2.ch.hat.i <- ave(eps.i^2, decile, FUN = mean))
    
    x1<-data.s$sig2.ch.hat.i # Iterated residual variances
    
    # Iterated 2nd & 3rd variance components
    
    # sigma2.2<-Var.Com.MM.2.H(data.s$ID.C,data.s$ID.H,eta.i,data.s$eps.i)$sigma2.2
    sig2.HT.i<-Var.Com.MM.3.H(level.3=data.s$ID.D,level.2=data.s$ID.C,level.1=data.s$ID.H,res.3=v.i,res.2=eta.i,con.res.1=data.s$eps.i)
    sigma2.2<-sig2.HT.i$sigma2.2  # Initial 2nd variance component
    sigma2.3<-sig2.HT.i$sigma2.3
    
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
  
  # Ultimate 2nd & 3rd variance components using IGLS method
  
  sigma2.3.HT.IGLS<-sigma2.3
  sigma2.2.HT.IGLS<-sigma2.2
  # Estimation of Residual variances for population individuals
  
  N<-ifelse (is.vector(x.U), length(x.U), dim(x.U)[1])
  
  X.U<-cbind(rep(1,N),x.U)
  
  data.U<-data.frame(ID.D=ID.D.U,ID.C=ID.C.U,ID.H=ID.H.U)
  data.U$y.fixed<-X.U%*%beta.igls
  
  cut.U<-y.decile
  
  # Capturing the minimum and maximum predicted values which are out of the estimated cut.off points
  
  cut.U[1]<-min(data.U$y.fixed,na.rm=TRUE)
  cut.U[length(cut.U)]<-max(data.U$y.fixed,na.rm=TRUE)
  
  # now creating the groups on the basis of cut.off points
  
  data.U<-within(data.U, decile <- as.integer(cut(y.fixed, cut.U,include.lowest=TRUE)))
  
  data.U<-data.U[order(data.U$decile),]
  
  data.U<-within(data.U, sig2.ch.hat <- rep(sig2.ch.decile,as.vector(table(data.U$decile))))
  
  data.U<-data.U[order(data.U$ID.C,data.U$ID.H),]
  
  sig2.ch.hat.U<-data.U$sig2.ch.hat
  
  list(iteration=i,beta.igls=beta.igls,vcov.beta.igls=vcov.beta.igls,
       sig2.ch.hat.s=sig2.ch.hat.s,sig2.ch.hat.U=sig2.ch.hat.U,sigma2.2.HT.IGLS=sigma2.2.HT.IGLS,sigma2.3.HT.IGLS=sigma2.3.HT.IGLS)
}
# ------------------------------------------------------------------------------
# PELL: ELL methodology via Parametric Bootstrap procedure: Homoskedasticity & Heteroskedasticity  
# ------------------------------------------------------------------------------
ELL.PB.HM.2L.FGT.Estimator<- function(beta,var.beta,var.com.1,var.com.2,ID.D,ID.C,X.U,t,HH.Size,No.Boot){
  
  # Validation
  #beta<-beta.gls.2;var.beta<-var.beta.gls.2;var.com.1<-est.sigma2.2$sigma2.1;var.com.2<-est.sigma2.2$sigma2.2;
  #ID.D<-Census.data.fitted$ID.UPZ;ID.C<-Census.data.fitted$psu;
  #X.U<-x.matrix.U; t<-Census.data.fitted$lpovln;HH.Size<-Census.data.fitted$HH.size.U
  
  # This function is for estimating FGT estimates under ELL HM
  # Considering HH Size, No HH size put HH.Size=NULL
  # Basic ELL Parametric method considering Homoskedastic Variance components
  # t is a value or a vector : It should be in original form
  # ID.D, ID.C,X.U,t,HH.Size all correspond to HH-level information
  # All variables are ordered according to ID.D
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  N.c<-as.vector(table(ID.C))
  N.d<-as.vector(table(ID.D))
  C<-length(unique(ID.C))
  
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    eta.l<-rnorm(C,0,sqrt(var.com.2))
    eps.l<-rnorm(N,0,sqrt(var.com.1))
    
    if (is.null(X.U)) z.l<-cbind(rep(1,N))%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    if (! is.null(X.U)) z.l<-as.matrix(cbind(rep(1,N),X.U))%*%t(beta.l)+rep(eta.l,N.c)+eps.l # z.l is in logarithm scale
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
      
    }
    
    if (! is.null(HH.Size)) {
      
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(Area.ID=unique(ID.D),
       F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
}
# ------------------------------------------------------------------------------
ELL.PB.HM.3L.FGT.Estimator<- function(beta,var.beta,var.com.1,var.com.2,var.com.3,ID.D,ID.C,X.U,t,HH.Size,No.Boot){
  
  # This function is for estimating FGT estimates
  # Basic ELL Parametric method considering Homoskedastic Variance components
  # t is a value or a vector : It should be in original form
  # y.l is in original scale
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  
  N<-length(ID.D)
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  N.d<-as.vector(table(ID.D))
  D<-length(unique(ID.D))
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    
    u.l<-rnorm(D,0,sqrt(var.com.3))
    eta.l<-rnorm(C,0,sqrt(var.com.2))
    eps.l<-rnorm(N,0,sqrt(var.com.1))
    
    if (is.null(X.U)) z.l<-cbind(rep(1,N))%*%t(beta.l)+rep(u.l,N.d)+rep(eta.l,N.c)+eps.l
    if (! is.null(X.U)) z.l<-as.matrix(cbind(rep(1,N),X.U))%*%t(beta.l)+rep(u.l,N.d)+rep(eta.l,N.c)+eps.l # z.l is in logarithm scale
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
      
    }
    
    if (! is.null(HH.Size)) {
      
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
}
# ------------------------------------------------------------------------------
ELL.PB.HT.2L.FGT.Estimator<- function(beta,var.beta,alpha,var.alpha,sigma2.alpha,var.com.2,ID.D,ID.C,X.U.HT,X.U,A,t,HH.Size,No.Boot){
  # Parametric Bootstrap procedure
  # This function is for estimating FGT estimates
  # Basic ELL Parametric method considering Heteroskedastic Variance component
  # t is here a value but need to be a vector
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    alpha.l<-mvtnorm::rmvnorm(1,alpha,var.alpha)
    B <- exp(cbind(rep(1,N),X.U.HT)%*%t(alpha.l))
    var.com.HH.U <- A*B/(1+B) + 0.5*sigma2.alpha*(A*B)*(1-B)/((1+B)^3)
    
    eta.l<-rnorm(C,0,sqrt(var.com.2))
    eps.l<-rnorm(N,0,sqrt(var.com.HH.U))
    
    
    if (is.null(X.U)) z.l<-cbind(rep(1,N))%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    if (! is.null(X.U)) z.l<-as.matrix(cbind(rep(1,N),X.U))%*%t(beta.l)+rep(eta.l,N.c)+eps.l # z.l is in logarithm scale
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
      
    }
    
    if (! is.null(HH.Size)) {
      
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
}
# ------------------------------------------------------------------------------
ELL.PB.HT.3L.FGT.Estimator<- function(beta,var.beta,alpha,var.alpha,sigma2.alpha,var.com.2,var.com.3,ID.D,ID.C,X.U.HT,X.U,A,t,HH.Size,No.Boot){
  # Parametric Bootstrap procedure
  # This function is for estimating FGT estimates
  # Basic ELL Parametric method considering Heteroskedastic Variance component
  # t is here a value but need to be a vector
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  N.d<-as.vector(table(ID.D))
  D<-length(unique(ID.D))
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    alpha.l<-mvtnorm::rmvnorm(1,alpha,var.alpha)
    B <- exp(cbind(rep(1,N),X.U.HT)%*%t(alpha.l))
    var.com.HH.U <- A*B/(1+B) + 0.5*sigma2.alpha*(A*B)*(1-B)/((1+B)^3)
    
    u.l<-rnorm(D,0,sqrt(var.com.3))
    eta.l<-rnorm(C,0,sqrt(var.com.2))
    eps.l<-rnorm(N,0,sqrt(var.com.HH.U))
    
    if (is.null(X.U)) z.l<-cbind(rep(1,N))%*%t(beta.l)+rep(u.l,N.d)+rep(eta.l,N.c)+eps.l
    if (! is.null(X.U)) z.l<-as.matrix(cbind(rep(1,N),X.U))%*%t(beta.l)+rep(u.l,N.d)+rep(eta.l,N.c)+eps.l # z.l is in logarithm scale
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
      
    }
    
    if (! is.null(HH.Size)) {
      
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
  
}
# ------------------------------------------------------------------------------
# NPELL: ELL methodology via Non-Parametric Bootstrap procedure: Homoskedasticity  
# ------------------------------------------------------------------------------
ELL.NPB.HM.2L.FGT.Estimator.Scale<- function(beta,var.beta,eta.s,eps.s,var.com.1,var.com.2,ID.C.s,ID.D,ID.C,X.U,t,HH.Size,No.Boot,residual.1=c("unconditional","conditional")){
  
  # This function is for estimating FGT estimates
  # Basic ELL Non/Semi Parametric method considering Homoskedastic Variance components
  # t is here a value but need to be a vector
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  eta.u.scl<-eta.s*scale.2
  
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  eps.s.scl<-eps.s*scale.1
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    
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
    
    z.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
  
}
# ------------------------------------------------------------------------------
ELL.NPB.HM.3L.FGT.Estimator.Scale<- function(beta,var.beta,jeta.s,eta.s,eps.s,var.com.1,var.com.2,var.com.3,ID.C.s,ID.D.s,ID.D,ID.C,X.U,t,HH.Size,No.Boot,residual.1=c("unconditional","conditional")){
  
  # This function is for estimating FGT estimates
  # Basic ELL Non/Semi Parametric method considering Homoskedastic Variance components
  # t is here a value but need to be a vector
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  N.d<-as.vector(table(ID.D))
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  D<-length(unique(ID.D))
  
  C.d<-NULL
  for (d in unique(ID.D)) C.d<-c(C.d,length(unique(ID.C[ID.D==d])))
  
  scale.3<-sqrt(var.com.3/(sum(jeta.s^2)/(length(jeta.s)-1)))
  jeta.u.scl<-jeta.s*scale.3
  
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  eta.u.scl<-eta.s*scale.2
  
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  eps.s.scl<-eps.s*scale.1
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    
    if (residual.1=="unconditional") {
      jeta.l<-sample(jeta.u.scl,D,replace=TRUE)
      eta.l<-sample(eta.u.scl,C,replace=TRUE)
      eps.l<-sample(eps.s.scl,N,replace=TRUE)
    }
    
    if (residual.1=="conditional") {
      
      ID.D.sampling<-sample(c(1:length(unique(ID.D.s))),D,replace=TRUE)
      jeta.l<-jeta.u.scl[ID.D.sampling]
      
      ID.C.sampling<-NULL
      for (d in 1:D){
        no.cl.d<-length(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]))
        if(no.cl.d>1) {ID.C.sampling.d<-sample(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]),C.d[d],replace=TRUE)} else {ID.C.sampling.d<-rep(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]),C.d[d])}
        ID.C.sampling<-c(ID.C.sampling,ID.C.sampling.d)
      }
      
      eta.l<-eta.u.scl[ID.C.sampling]
      
      ID.C.sampled<-unique(ID.C.s)[ID.C.sampling]
      
      eps.l<-NULL
      for (c in 1:C){
        eps.U<-sample(eps.s.scl[ID.C.s==ID.C.sampled[c]],N.c[c],replace=TRUE)
        eps.l<-c(eps.l,eps.U)
      }
      
    }
    
    z.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(jeta.l,N.d)+rep(eta.l,N.c)+eps.l
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
  
}
# ------------------------------------------------------------------------------
# SPELL: ELL methodology via Semi-Parametric Bootstrap procedure: Heteroskedasticity (with Scaled and Raw Residuals)
# ------------------------------------------------------------------------------
ELL.NPB.HT.2L.FGT.Estimator<- function(beta,var.beta,alpha,var.alpha,sigma2.alpha,eta.s,eps.s,sig2.eps.s,ID.C.s,ID.D,ID.C,X.U.HT,X.U,A,t,HH.Size,No.Boot,residual.1=c("unconditional","conditional")){
  
  # Non-parametric Bootstrap procedure (ELL, 2002,2003)
  # This function is for estimating Distribution function
  # Heteroskedastic error variances based on logistic function
  # t is here a value but need to be a vector
  # Conditional: Draw individual level effects for a population cluster from the sample cluster whose random effect is randomly drawn for the population cluster
  # Unconditional: Draw without restriction of drawing cluster random effects
  # eta.s should be ordered in ID.C.s
  # eps.s and sig2.eps.s should be ordered in ID.C.s
  # Sample and population data sets should be ordered by area and clusters
  # Raw residuals
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  N.d<-as.vector(table(ID.D))
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  # standardized the residuals using the individual specific residuals
  eps.std<-eps.s/sqrt(sig2.eps.s)-mean(eps.s/sqrt(sig2.eps.s))
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    alpha.l<-mvtnorm::rmvnorm(1,alpha,var.alpha)
    B <- exp(cbind(rep(1,N),X.U.HT)%*%t(alpha.l))
    var.com.HH.U <- A*B/(1+B) + 0.5*sigma2.alpha*(A*B)*(1-B)/((1+B)^3)
    
    
    
    if (residual.1=="unconditional") {
      eta.l<-sample(eta.s,C,replace=TRUE)
      eps.u.std<-sample(eps.std,N,replace=TRUE)
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
      
    }
    
    eps.l<-eps.u.std*sqrt(var.com.HH.U)
    
    z.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
}
# ------------------------------------------------------------------------------
ELL.NPB.HT.2L.FGT.Estimator.Scale<- function(beta,var.beta,alpha,var.alpha,sigma2.alpha,eta.s,eps.s,var.com.2,var.com.1,sig2.eps.s,ID.C.s,ID.D,ID.C,X.U.HT,X.U,A,t,HH.Size,No.Boot,residual.1=c("unconditional","conditional")){
  
  # Non-parametric Bootstrap procedure (ELL, 2002,2003)
  # This function is for estimating Distribution function
  # Heteroskedastic error variances based on logistic function
  # t is here a value but need to be a vector
  # Conditional: Draw individual level effects for a population cluster from the sample cluster whose random effect is randomly drawn for the population cluster
  # Unconditional: Draw without restriction of drawing cluster random effects
  # eta.s should be ordered in ID.C.s
  # eps.s and sig2.eps.s should be ordered in ID.C.s
  # Sample and population data sets should be ordered by area and clusters
  # Scaled residuals
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  N.d<-as.vector(table(ID.D))
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  eta.u.scl<-eta.s*scale.2
  
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  eps.s.scl<-eps.s*scale.1
  
  # standardized the residuals using the individual specific residuals
  eps.std<-eps.s.scl/sqrt(sig2.eps.s)-mean(eps.s.scl/sqrt(sig2.eps.s))
  
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    alpha.l<-mvtnorm::rmvnorm(1,alpha,var.alpha)
    B <- exp(cbind(rep(1,N),X.U.HT)%*%t(alpha.l))
    var.com.HH.U <- A*B/(1+B) + 0.5*sigma2.alpha*(A*B)*(1-B)/((1+B)^3)
    
    
    
    if (residual.1=="unconditional") {
      eta.l<-sample(eta.u.scl,C,replace=TRUE)
      eps.u.std<-sample(eps.std,N,replace=TRUE)
    }
    
    if (residual.1=="conditional") {
      ID.C.sampling<-sample(c(1:length(unique(ID.C.s))),C,replace=TRUE)
      eta.l<-eta.u.scl[ID.C.sampling]
      
      ID.C.sampled<-unique(ID.C.s)[ID.C.sampling]
      
      eps.u.std<-NULL
      for (c in 1:C){
        eps.U<-sample(eps.std[ID.C.s==ID.C.sampled[c]],N.c[c],replace=TRUE)
        eps.u.std<-c(eps.u.std,eps.U)
      }
      
    }
    
    eps.l<-eps.u.std*sqrt(var.com.HH.U)
    
    z.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
}
# ------------------------------------------------------------------------------
ELL.NPB.HT.3L.FGT.Estimator<- function(beta,var.beta,alpha,var.alpha,sigma2.alpha,jeta.s,eta.s,eps.s,sig2.eps.s,ID.C.s,ID.D.s,ID.D,ID.C,X.U.HT,X.U,A,t,HH.Size,No.Boot,residual.1=c("unconditional","conditional")){
  
  # Non-parametric Bootstrap procedure (ELL, 2002,2003)
  # This function is for estimating Distribution function
  # Heteroskedastic error variances based on logistic function
  # t is here a value but need to be a vector
  # Conditional: Draw individual level effects for a population cluster from the sample cluster whose random effect is randomly drawn for the population cluster
  # Unconditional: Draw without restriction of drawing cluster random effects
  # eta.s should be ordered in ID.C.s
  # eps.s and sig2.eps.s should be ordered in ID.C.s
  # Sample and population data sets should be ordered by area and clusters
  # Raw residuals
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  N.d<-as.vector(table(ID.D))
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  D<-length(unique(ID.D))
  C.d<-NULL
  for (d in unique(ID.D)) C.d<-c(C.d,length(unique(ID.C[ID.D==d])))
  
  # standardized the residuals using the individual specific residuals
  eps.std<-eps.s/sqrt(sig2.eps.s)-mean(eps.s/sqrt(sig2.eps.s))
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    alpha.l<-mvtnorm::rmvnorm(1,alpha,var.alpha)
    B <- exp(cbind(rep(1,N),X.U.HT)%*%t(alpha.l))
    var.com.HH.U <- A*B/(1+B) + 0.5*sigma2.alpha*(A*B)*(1-B)/((1+B)^3)
    
    if (residual.1=="unconditional") {
      jeta.l<-sample(jeta.s,D,replace=TRUE)
      eta.l<-sample(eta.s,C,replace=TRUE)
      eps.u.std<-sample(eps.std,N,replace=TRUE)
    }
    
    if (residual.1=="conditional") {
      
      ID.D.sampling<-sample(c(1:length(unique(ID.D.s))),D,replace=TRUE)
      jeta.l<-jeta.s[ID.D.sampling]
      
      ID.C.sampling<-NULL
      for (d in 1:D){
        no.cl.d<-length(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]))
        if(no.cl.d>1) {ID.C.sampling.d<-sample(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]),C.d[d],replace=TRUE)} else {ID.C.sampling.d<-rep(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]),C.d[d])}
        ID.C.sampling<-c(ID.C.sampling,ID.C.sampling.d)
      }
      
      eta.l<-eta.s[ID.C.sampling]
      
      ID.C.sampled<-unique(ID.C.s)[ID.C.sampling]
      
      eps.u.std<-NULL
      for (c in 1:C){
        eps.U<-sample(eps.std[ID.C.s==ID.C.sampled[c]],N.c[c],replace=TRUE)
        eps.u.std<-c(eps.u.std,eps.U)
      }
      
    }
    
    eps.l<-eps.u.std*sqrt(var.com.HH.U)
    
    z.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(jeta.l,N.d)+rep(eta.l,N.c)+eps.l
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
}
# ------------------------------------------------------------------------------
ELL.NPB.HT.3L.FGT.Estimator.Scale<- function(beta,var.beta,alpha,var.alpha,sigma2.alpha,jeta.s,eta.s,eps.s,var.com.3,var.com.2,var.com.1,sig2.eps.s,ID.C.s,ID.D.s,ID.D,ID.C,X.U.HT,X.U,A,t,HH.Size,No.Boot,residual.1=c("unconditional","conditional")){
  
  # Non-parametric Bootstrap procedure (ELL, 2002,2003)
  # This function is for estimating Distribution function
  # Heteroskedastic error variances based on logistic function
  # t is here a value but need to be a vector
  # Conditional: Draw individual level effects for a population cluster from the sample cluster whose random effect is randomly drawn for the population cluster
  # Unconditional: Draw without restriction of drawing cluster random effects
  # eta.s should be ordered in ID.C.s
  # eps.s and sig2.eps.s should be ordered in ID.C.s
  # Sample and population data sets should be ordered by area and clusters
  # Scaled residuals
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  N.d<-as.vector(table(ID.D))
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  D<-length(unique(ID.D))
  C.d<-NULL
  for (d in unique(ID.D)) C.d<-c(C.d,length(unique(ID.C[ID.D==d])))
  
  scale.3<-sqrt(var.com.3/(sum(jeta.s^2)/(length(jeta.s)-1)))
  jeta.u.scl<-jeta.s*scale.3
  
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  eta.u.scl<-eta.s*scale.2
  
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  eps.s.scl<-eps.s*scale.1
  
  # standardized the residuals using the individual specific residuals
  eps.std<-eps.s.scl/sqrt(sig2.eps.s)-mean(eps.s.scl/sqrt(sig2.eps.s))
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    alpha.l<-mvtnorm::rmvnorm(1,alpha,var.alpha)
    B <- exp(cbind(rep(1,N),X.U.HT)%*%t(alpha.l))
    var.com.HH.U <- A*B/(1+B) + 0.5*sigma2.alpha*(A*B)*(1-B)/((1+B)^3)
    
    
    
    if (residual.1=="unconditional") {
      jeta.l<-sample(jeta.u.scl,D,replace=TRUE)
      eta.l<-sample(eta.u.scl,C,replace=TRUE)
      eps.u.std<-sample(eps.std,N,replace=TRUE)
    }
    
    if (residual.1=="conditional") {
      
      ID.D.sampling<-sample(c(1:length(unique(ID.D.s))),D,replace=TRUE)
      jeta.l<-jeta.u.scl[ID.D.sampling]
      
      ID.C.sampling<-NULL
      for (d in 1:D){
        no.cl.d<-length(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]))
        if(no.cl.d>1) {ID.C.sampling.d<-sample(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]),C.d[d],replace=TRUE)} else {ID.C.sampling.d<-rep(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]),C.d[d])}
        ID.C.sampling<-c(ID.C.sampling,ID.C.sampling.d)
      }
      
      eta.l<-eta.u.scl[ID.C.sampling]
      
      ID.C.sampled<-unique(ID.C.s)[ID.C.sampling]
      
      eps.u.std<-NULL
      for (c in 1:C){
        eps.U<-sample(eps.std[ID.C.s==ID.C.sampled[c]],N.c[c],replace=TRUE)
        eps.u.std<-c(eps.u.std,eps.U)
      }
      
    }
    
    eps.l<-eps.u.std*sqrt(var.com.HH.U)
    
    z.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(jeta.l,N.d)+rep(eta.l,N.c)+eps.l
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
}
# ------------------------------------------------------------------------------
# Mixed ELL Approach: PELL approach
# ------------------------------------------------------------------------------
Mixed.ELL.PB.HM.2L.3L.FGT.Estimator<- function(beta.2l,var.beta.2l,var.com.1.2l,var.com.2.2l,ID.D.2l,ID.C.2l,X.U.2l,t.2l,HH.Size.2l,
      beta.3l,var.beta.3l,var.com.1.3l,var.com.2.3l,var.com.3.3l,ID.D.3l,ID.C.3l,X.U.3l,t.3l,HH.Size.3l,No.Boot){
  # 2L model for rural areas and 3L model for Urban aeas

  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N.2l<-length(ID.D.2l)
  N.c.2l<-as.vector(table(ID.C.2l))
  N.d.2l<-as.vector(table(ID.D.2l))
  C.2l<-length(unique(ID.C.2l))
  
  N.3l<-length(ID.D.3l)
  N.c.3l<-as.vector(table(ID.C.3l))
  C.3l<-length(unique(ID.C.3l))
  N.d.3l<-as.vector(table(ID.D.3l))
  D.3l<-length(unique(ID.D.3l))
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l.2l<-mvtnorm::rmvnorm(1,beta.2l,var.beta.2l)
    eta.l.2l<-rnorm(C.2l,0,sqrt(var.com.2.2l))
    eps.l.2l<-rnorm(N.2l,0,sqrt(var.com.1.2l))
    
    beta.l.3l<-mvtnorm::rmvnorm(1,beta.3l,var.beta.3l)
    u.l.3l<-rnorm(D.3l,0,sqrt(var.com.3.3l))
    eta.l.3l<-rnorm(C.3l,0,sqrt(var.com.2.3l))
    eps.l.3l<-rnorm(N.3l,0,sqrt(var.com.1.3l))
    
    if (is.null(X.U.2l)) z.l.2l<-cbind(rep(1,N.2l))%*%t(beta.l.2l)+rep(eta.l.2l,N.c.2l)+eps.l.2l
    if (! is.null(X.U.2l)) z.l.2l<-as.matrix(cbind(rep(1,N.2l),X.U.2l))%*%t(beta.l.2l)+rep(eta.l.2l,N.c.2l)+eps.l.2l # z.l is in logarithm scale
    
    y.l.2l<-exp(z.l.2l) # y.l is in original scale
    
    if (is.null(X.U.3l)) z.l.3l<-cbind(rep(1,N.3l))%*%t(beta.l.3l)+rep(u.l.3l,N.d.3l)+rep(eta.l.3l,N.c.3l)+eps.l.3l
    if (! is.null(X.U.3l)) z.l.3l<-as.matrix(cbind(rep(1,N.3l),X.U.3l))%*%t(beta.l.3l)+rep(u.l.3l,N.d.3l)+rep(eta.l.3l,N.c.3l)+eps.l.3l # z.l is in logarithm scale
    
    y.l.3l<-exp(z.l.3l) # y.l is in original scale
    
    HH.Size<-as.vector(c(HH.Size.2l,HH.Size.3l))
    y.l<-as.vector(c(y.l.2l,y.l.3l))
    t<-as.vector(c(t.2l,t.3l))
    ID.D<-as.vector(c(ID.D.2l,ID.D.3l))
    
    
    if (is.null(HH.Size)) {
      
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
      
    }
    
    if (! is.null(HH.Size)) {
      
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
}
# ------------------------------------------------------------------------------
# CDMC: CD based method via MC simulation & non-parametric Bootstrap procedure: Homoskedasticity & Heteroskedasticity  
# ------------------------------------------------------------------------------
CD.MC.HM.2L.FGT.Estimator<-function(beta,var.beta,eta.s,eps.s,var.com.2,var.com.1,ID.C.s,ID.D,ID.C,X.U,t,HH.Size,No.Boot,residual.1=c("unconditional","conditional")){
  
  # Following the Marchetti et al (2012) as an alternative of CD approach
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  C<-length(unique(ID.C))
  N.c<-as.vector(table(ID.C))
  
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  
  eta.s.scl<-eta.s*scale.2
  eps.s.scl<-eps.s*scale.1
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    
    if (residual.1=="unconditional") {
      eta.l<-sample(eta.s.scl,C,replace=TRUE)
      eps.l<-sample(eps.s.scl,N,replace=TRUE)
    }
    
    if (residual.1=="conditional") {
      ID.C.sampling<-sample(c(1:length(unique(ID.C.s))),C,replace=TRUE)
      eta.l<-eta.s.scl[ID.C.sampling]
      
      ID.C.sampled<-unique(ID.C.s)[ID.C.sampling]
      
      eps.l<-NULL
      for (c in 1:C){
        eps.U<-sample(eps.s.scl[ID.C.s==ID.C.sampled[c]],N.c[c],replace=TRUE)
        eps.l<-c(eps.l,eps.U)
      }
      
    }
    
    if (is.null(X.U))   z.l<-cbind(rep(1,N))%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    if (! is.null(X.U)) z.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    
    y.l<-exp(z.l) # y.l is in original scale
    
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
  
}
# ------------------------------------------------------------------------------
CD.MC.HM.3L.FGT.Estimator<-function(beta,var.beta,jeta.s,eta.s,eps.s,var.com.3,var.com.2,var.com.1,ID.C.s,ID.D.s,ID.D,ID.C,X.U,t,HH.Size,No.Boot,residual.1=c("unconditional","conditional")){
  
  # Following the Marchetti et al (2012) as an alternative of CD approach
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  N.d<-as.vector(table(ID.D))
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  D<-length(unique(ID.D))
  
  C.d<-NULL
  for (d in unique(ID.D)) C.d<-c(C.d,length(unique(ID.C[ID.D==d])))
  
  scale.3<-sqrt(var.com.3/(sum(jeta.s^2)/(length(jeta.s)-1)))
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  
  jeta.s.scl<-jeta.s*scale.3
  eta.s.scl<-eta.s*scale.2
  eps.s.scl<-eps.s*scale.1
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    
    if (residual.1=="unconditional") {
      jeta.l<-sample(jeta.s.scl,D,replace=TRUE)
      eta.l<-sample(eta.s.scl,C,replace=TRUE)
      eps.l<-sample(eps.s.scl,N,replace=TRUE)
    }
    
    if (residual.1=="conditional") {
      
      ID.D.sampling<-sample(c(1:length(unique(ID.D.s))),D,replace=TRUE)
      jeta.l<-jeta.s.scl[ID.D.sampling]
      
      ID.C.sampling<-NULL
      for (d in 1:D){
        no.cl.d<-length(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]))
        if(no.cl.d>1) {ID.C.sampling.d<-sample(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]),C.d[d],replace=TRUE)} else {ID.C.sampling.d<-rep(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]),C.d[d])}
        ID.C.sampling<-c(ID.C.sampling,ID.C.sampling.d)
      }
      
      eta.l<-eta.s.scl[ID.C.sampling]
      
      ID.C.sampled<-unique(ID.C.s)[ID.C.sampling]
      
      eps.l<-NULL
      for (c in 1:C){
        eps.U<-sample(eps.s.scl[ID.C.s==ID.C.sampled[c]],N.c[c],replace=TRUE)
        eps.l<-c(eps.l,eps.U)
      }
      
    }
    
    if (is.null(HH.Size))   z.l<-cbind(rep(1,N))%*%t(beta.l)+rep(jeta.l,N.d)+rep(eta.l,N.c)+eps.l
    if (! is.null(HH.Size)) z.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(jeta.l,N.d)+rep(eta.l,N.c)+eps.l
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
  
}
# ------------------------------------------------------------------------------
CD.MC.HT.2L.FGT.Estimator.Scale<-function(beta,var.beta,eta.s,eps.s,var.com.2,var.com.1,var.com.HH.s,var.com.HH.U,ID.C.s,ID.D,ID.C,X.U,t,HH.Size,No.Boot,residual.1=c("unconditional","conditional")){
  
  # Following the Marchetti et al (2012) as an alternative of CD approach
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  C<-length(unique(ID.C))
  N.c<-as.vector(table(ID.C))
  
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  eta.s.scl<-eta.s*scale.2
  
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  eps.s.scl<-eps.s*scale.1
  
  std.eps.s<-eps.s.scl/sqrt(var.com.HH.s)#-mean(eps.s.scl/sqrt(var.com.HH.s))
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    
    if (residual.1=="unconditional") {
      eta.l<-sample(eta.s.scl,C,replace=TRUE)
      eps.u.std<-sample(std.eps.s,N,replace=TRUE)
    }
    
    if (residual.1=="conditional") {
      ID.C.sampling<-sample(c(1:length(unique(ID.C.s))),C,replace=TRUE)
      eta.l<-eta.s.scl[ID.C.sampling]
      
      ID.C.sampled<-unique(ID.C.s)[ID.C.sampling]
      
      eps.u.std<-NULL
      for (c in 1:C){
        eps.U<-sample(std.eps.s[ID.C.s==ID.C.sampled[c]],N.c[c],replace=TRUE)
        eps.u.std<-c(eps.u.std,eps.U)
      }
      
    }
    
    eps.l<- eps.u.std*sqrt(var.com.HH.U)
    
    if (is.null(X.U))   z.l<-cbind(rep(1,N))%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    if (! is.null(X.U)) z.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
}
# ------------------------------------------------------------------------------
CD.MC.HT.3L.FGT.Estimator.Scale<-function(beta,var.beta,jeta.s,eta.s,eps.s,var.com.3,var.com.2,var.com.1,var.com.HH.s,var.com.HH.U,ID.C.s,ID.D.s,ID.D,ID.C,X.U,t,HH.Size,No.Boot,residual.1=c("unconditional","conditional")){
  
  # Following the Marchetti et al (2012) as an alternative of CD approach
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  N.d<-as.vector(table(ID.D))
  N.c<-as.vector(table(ID.C))
  C<-length(unique(ID.C))
  D<-length(unique(ID.D))
  
  C.d<-NULL
  for (d in unique(ID.D)) C.d<-c(C.d,length(unique(ID.C[ID.D==d])))
  
  scale.3<-sqrt(var.com.3/(sum(jeta.s^2)/(length(jeta.s)-1)))
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  
  jeta.s.scl<-jeta.s*scale.3
  eta.s.scl<-eta.s*scale.2
  eps.s.scl<-eps.s*scale.1
  
  # standardized the residuals using the individual specific residuals
  
  std.eps.s<-eps.s.scl/sqrt(var.com.HH.s) #-mean(eps.s.scl/sqrt(var.com.HH.s))
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    
    #  eta.u<-sample(eta.s,C,replace=TRUE)
    #  eps.u.l<-sample(std.eps.s,N,replace=TRUE)
    
    if (residual.1=="unconditional") {
      jeta.l<-sample(jeta.s.scl,D,replace=TRUE)
      eta.l<-sample(eta.s.scl,C,replace=TRUE)
      eps.u.std<-sample(std.eps.s,N,replace=TRUE)
    }
    
    if (residual.1=="conditional") {
      
      ID.D.sampling<-sample(c(1:length(unique(ID.D.s))),D,replace=TRUE)
      jeta.l<-jeta.s.scl[ID.D.sampling]
      
      ID.C.sampling<-NULL
      for (d in 1:D){
        no.cl.d<-length(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]))
        if(no.cl.d>1) {ID.C.sampling.d<-sample(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]),C.d[d],replace=TRUE)} else {ID.C.sampling.d<-rep(unique(ID.C.s[ID.D.s==ID.D.sampling[d]]),C.d[d])}
        ID.C.sampling<-c(ID.C.sampling,ID.C.sampling.d)
      }
      
      eta.l<-eta.s.scl[ID.C.sampling]
      
      ID.C.sampled<-unique(ID.C.s)[ID.C.sampling]
      
      eps.u.std<-NULL
      for (c in 1:C){
        eps.U<-sample(std.eps.s[ID.C.s==ID.C.sampled[c]],N.c[c],replace=TRUE)
        eps.u.std<-c(eps.u.std,eps.U)
      }
      
    }
    
    eps.l<- eps.u.std*sqrt(var.com.HH.U)
    
    if (is.null(X.U))   z.l<-cbind(rep(1,N))%*%t(beta.l)+rep(jeta.l,N.d)+rep(eta.l,N.c)+eps.l
    if (! is.null(X.U)) z.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(jeta.l,N.d)+rep(eta.l,N.c)+eps.l
    
    y.l<-exp(z.l) # y.l is in original scale
    
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
}
# ------------------------------------------------------------------------------
# CDSM: CD based method via SM approach & non-parametric Bootstrap procedure: Homoskedasticity & Heteroskedasticity  
# ------------------------------------------------------------------------------
CD.SM.HM.2L.FGT.Estimator<-function(beta,var.beta,eta.s,eps.s,var.com.2,var.com.1,ID.D,ID.C,ID.HH,X.U,t,HH.Size,No.Boot,residual.1=c("Fixed","Random")){
  
  # CD estimator for both Homogeneous variance component
  # 2nd level Residuals are scaled
  # t is here a value but need to be a vector
  # var.com.1 and var.com.1.U are scalar for scaling
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  No.Area<-length(unique(ID.D))
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  
  eta.u.scl<-eta.s*scale.2
  eps.s.scl<-eps.s*scale.1
  std.eps.s<-eps.s.scl/sqrt(var.com.1)
  
  n<-length(eps.s)
  
  F0.F11<-rep(0,No.Area)
  F0.F11.MSE<-rep(0,No.Area)
  F0.F11.Q.02.5<-rep(0,No.Area)
  F0.F11.Q.97.5<-rep(0,No.Area)
  
  F1.F11<-rep(0,No.Area)
  F1.F11.MSE<-rep(0,No.Area)
  F1.F11.Q.02.5<-rep(0,No.Area)
  F1.F11.Q.97.5<-rep(0,No.Area)
  
  F2.F11<-rep(0,No.Area)
  F2.F11.MSE<-rep(0,No.Area)
  F2.F11.Q.02.5<-rep(0,No.Area)
  F2.F11.Q.97.5<-rep(0,No.Area)
  
  for (d in 1:No.Area){
    
    cat(date(),"Iteration number",d,"starting","\n",fill=T)
    
    N.d<-length(ID.D[ID.D==d])
    N.c<-as.vector(table(ID.C[ID.D==d])) # sum(N.c)
    Cluster.c<-length(N.c)
    X.U.d<-X.U[ID.HH[ID.D==d],]
    t.d<-t[ID.D==d]
    HH.Size.d<-HH.Size[ID.D==d]
    
    r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
      
      beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
      eta.l<-as.vector(sample(eta.u.scl,Cluster.c,replace=TRUE))
      
      if (residual.1=="Fixed") eps.l<-as.vector(std.eps.s)
      if (residual.1=="Random") eps.l<-sample(as.vector(std.eps.s),n,replace=TRUE)
      
      if (is.null(HH.Size)) {
        
        z.l<-as.vector(cbind(rep(1,N.d),X.U.d)%*%t(beta.l))+rep(eta.l,N.c)+outer(sqrt(rep(var.com.1,N.d)),as.vector(eps.l))
        y.l<-exp(z.l) # y.l is in original scale
        
        AA<-y.l<t.d
        F0.t<-rowMeans(AA)
        
        B<-y.l
        B[which(B<0)]<-0
        BB<-((t.d-B)/t.d)*AA
        F1.t<-rowMeans(BB)
        
        CC<-((t.d-B)/t.d)^2*AA
        F2.t<-rowMeans(CC)
        
        FGT0<-mean(F0.t)
        FGT1<-mean(F1.t)
        FGT2<-mean(F2.t)
        
        list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
        
      }
      
      if (! is.null(HH.Size)) {
        
        z.l<-as.vector(cbind(rep(1,N.d),X.U.d)%*%t(beta.l))+rep(eta.l,N.c)+outer(sqrt(rep(var.com.1,N.d)),as.vector(eps.l))
        y.l<-exp(z.l) # y.l is in original scale
        
        AA<-y.l<t.d
        F0.t<-rowMeans(AA)
        
        B<-y.l
        B[which(B<0)]<-0
        BB<-((t.d-B)/t.d)*AA
        F1.t<-rowMeans(BB)
        
        CC<-((t.d-B)/t.d)^2*AA
        F2.t<-rowMeans(CC)
        
        FGT0<-sum(HH.Size.d*F0.t)/sum(HH.Size.d)
        FGT1<-sum(HH.Size.d*F1.t)/sum(HH.Size.d)
        FGT2<-sum(HH.Size.d*F2.t)/sum(HH.Size.d)
        
        list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
      }
      
    }
    
    F0.F11[d]<-apply(r.FGT$FGT0,2,mean)
    F0.F11.MSE[d]<-apply(r.FGT$FGT0,2,sd)
    F0.F11.Q.02.5[d]<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F0.F11.Q.97.5[d]<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
    F1.F11[d]<-apply(r.FGT$FGT1,2,mean)
    F1.F11.MSE[d]<-apply(r.FGT$FGT1,2,sd)
    F1.F11.Q.02.5[d]<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F1.F11.Q.97.5[d]<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
    F2.F11[d]<-apply(r.FGT$FGT2,2,mean)
    F2.F11.MSE[d]<-apply(r.FGT$FGT2,2,sd)
    F2.F11.Q.02.5[d]<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F2.F11.Q.97.5[d]<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
  }
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
}
# ------------------------------------------------------------------------------
CD.SM.HM.3L.FGT.Estimator<-function(beta,var.beta,jeta.s,eta.s,eps.s,var.com.3,var.com.2,var.com.1,ID.D,ID.C,ID.HH,X.U,t,HH.Size,No.Boot,residual.1=c("Fixed","Random")){
  
  # CD estimator for both Homogeneous variance component
  # 2nd level Residuals are scaled
  # t is here a value but need to be a vector
  # var.com.1 and var.com.1.U are scalar for scaling
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  No.Area<-length(unique(ID.D))
  
  scale.3<-sqrt(var.com.3/(sum(jeta.s^2)/(length(jeta.s)-1)))
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  
  jeta.s.scl<-jeta.s*scale.3
  eta.s.scl<-eta.s*scale.2
  eps.s.scl<-eps.s*scale.1
  
  std.eps.s<-eps.s.scl/sqrt(var.com.1)
  
  n<-length(eps.s)
  
  F0.F11<-rep(0,No.Area)
  F0.F11.MSE<-rep(0,No.Area)
  F0.F11.Q.02.5<-rep(0,No.Area)
  F0.F11.Q.97.5<-rep(0,No.Area)
  
  F1.F11<-rep(0,No.Area)
  F1.F11.MSE<-rep(0,No.Area)
  F1.F11.Q.02.5<-rep(0,No.Area)
  F1.F11.Q.97.5<-rep(0,No.Area)
  
  F2.F11<-rep(0,No.Area)
  F2.F11.MSE<-rep(0,No.Area)
  F2.F11.Q.02.5<-rep(0,No.Area)
  F2.F11.Q.97.5<-rep(0,No.Area)
  
  for (d in 1:No.Area){
    
    cat(date(),"Iteration number",d,"starting","\n",fill=T)
    
    N.d<-length(ID.D[ID.D==d])
    N.c<-as.vector(table(ID.C[ID.D==d])) # sum(N.c)
    Cluster.c<-length(N.c)
    X.U.d<-X.U[ID.HH[ID.D==d],]
    t.d<-t[ID.D==d]
    HH.Size.d<-HH.Size[ID.D==d]
    
    r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
      
      beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
      eta.l<-as.vector(sample(eta.s.scl,Cluster.c,replace=TRUE))
      jeta.l<-sample(jeta.s.scl,1,replace=TRUE)
      
      if (residual.1=="Fixed") eps.l<-as.vector(std.eps.s)
      if (residual.1=="Random") eps.l<-sample(as.vector(std.eps.s),n,replace=TRUE)
      
      if (is.null(HH.Size)) {
        z.l<-as.vector(cbind(rep(1,N.d),X.U.d)%*%t(beta.l))+rep(jeta.l,N.d)+rep(eta.l,N.c)+outer(sqrt(rep(var.com.1,N.d)),as.vector(eps.l))
        y.l<-exp(z.l) # y.l is in original scale
        
        AA<-y.l<t.d
        F0.t<-rowMeans(AA)
        
        B<-y.l
        B[which(B<0)]<-0
        BB<-((t.d-B)/t.d)*AA
        F1.t<-rowMeans(BB)
        
        CC<-((t.d-B)/t.d)^2*AA
        F2.t<-rowMeans(CC)
        
        FGT0<-mean(F0.t)
        FGT1<-mean(F1.t)
        FGT2<-mean(F2.t)
        
        list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
      }
      
      if (! is.null(HH.Size)) {
        
        z.l<-as.vector(cbind(rep(1,N.d),X.U.d)%*%t(beta.l))+rep(jeta.l,N.d)+rep(eta.l,N.c)+outer(sqrt(rep(var.com.1,N.d)),as.vector(eps.l))
        y.l<-exp(z.l) # y.l is in original scale
        
        AA<-y.l<t.d
        F0.t<-rowMeans(AA)
        
        B<-y.l
        B[which(B<0)]<-0
        BB<-((t.d-B)/t.d)*AA
        F1.t<-rowMeans(BB)
        
        CC<-((t.d-B)/t.d)^2*AA
        F2.t<-rowMeans(CC)
        
        FGT0<-sum(HH.Size.d*F0.t)/sum(HH.Size.d)
        FGT1<-sum(HH.Size.d*F1.t)/sum(HH.Size.d)
        FGT2<-sum(HH.Size.d*F2.t)/sum(HH.Size.d)
        
        list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
      }
      
    }
    
    F0.F11[d]<-apply(r.FGT$FGT0,2,mean)
    F0.F11.MSE[d]<-apply(r.FGT$FGT0,2,sd)
    F0.F11.Q.02.5[d]<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F0.F11.Q.97.5[d]<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
    F1.F11[d]<-apply(r.FGT$FGT1,2,mean)
    F1.F11.MSE[d]<-apply(r.FGT$FGT1,2,sd)
    F1.F11.Q.02.5[d]<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F1.F11.Q.97.5[d]<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
    F2.F11[d]<-apply(r.FGT$FGT2,2,mean)
    F2.F11.MSE[d]<-apply(r.FGT$FGT2,2,sd)
    F2.F11.Q.02.5[d]<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F2.F11.Q.97.5[d]<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
  }
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
}
# ------------------------------------------------------------------------------
CD.SM.HT.2L.FGT.Estimator.Scale<-function(beta,var.beta,eta.s,eps.s,var.com.2,var.com.1,var.com.HH.s,var.com.HH.U,ID.D,ID.C,ID.HH,X.U,t,HH.Size,No.Boot,residual.1=c("Fixed","Random")){
  
  # CD estimator for both Homogeneous variance component
  # 2nd level Residuals are scaled
  # t is here a value but need to be a vector
  # var.com.1 and var.com.1.U are scalar for scaling
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  No.Area<-length(unique(ID.D))
  
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  
  eta.s.scl<-eta.s*scale.2
  eps.s.scl<-eps.s*scale.1
  
  std.eps.s<-eps.s.scl/sqrt(var.com.HH.s)
  
  n<-length(eps.s)
  
  F0.F11<-rep(0,No.Area)
  F0.F11.MSE<-rep(0,No.Area)
  F0.F11.Q.02.5<-rep(0,No.Area)
  F0.F11.Q.97.5<-rep(0,No.Area)
  
  F1.F11<-rep(0,No.Area)
  F1.F11.MSE<-rep(0,No.Area)
  F1.F11.Q.02.5<-rep(0,No.Area)
  F1.F11.Q.97.5<-rep(0,No.Area)
  
  F2.F11<-rep(0,No.Area)
  F2.F11.MSE<-rep(0,No.Area)
  F2.F11.Q.02.5<-rep(0,No.Area)
  F2.F11.Q.97.5<-rep(0,No.Area)
  
  for (d in 1:No.Area){
    
    cat(date(),"Iteration number",d,"starting","\n",fill=T)
    
    N.d<-length(ID.D[ID.D==d])
    N.c<-as.vector(table(ID.C[ID.D==d])) # sum(N.c)
    Cluster.c<-length(N.c)
    X.U.d<-X.U[ID.HH[ID.D==d],]
    t.d<-t[ID.D==d]
    HH.Size.d<-HH.Size[ID.HH[ID.D==d]]
    var.com.HH.U.d<-var.com.HH.U[ID.HH[ID.D==d]]
    
    r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
      
      beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
      eta.l<-as.vector(sample(eta.s,Cluster.c,replace=TRUE))
      
      
      if (residual.1=="Fixed") eps.l<-as.vector(std.eps.s)
      if (residual.1=="Random") eps.l<-sample(as.vector(std.eps.s),n,replace=TRUE)
      
      if (is.null(HH.Size)) {
        
        z.l<-as.vector(cbind(rep(1,N.d),X.U.d)%*%t(beta.l))+rep(eta.l,N.c)+outer(sqrt(var.com.HH.U.d),as.vector(eps.l))
        y.l<-exp(z.l) # y.l is in original scale
        
        AA<-y.l<t.d
        F0.t<-rowMeans(AA)
        
        B<-y.l
        B[which(B<0)]<-0
        BB<-((t.d-B)/t.d)*AA
        F1.t<-rowMeans(BB)
        
        CC<-((t.d-B)/t.d)^2*AA
        F2.t<-rowMeans(CC)
        
        FGT0<-mean(F0.t)
        FGT1<-mean(F1.t)
        FGT2<-mean(F2.t)
        
        list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
      }
      
      if (! is.null(HH.Size)) {
        
        z.l<-as.vector(cbind(rep(1,N.d),X.U.d)%*%t(beta.l))+rep(eta.l,N.c)+outer(sqrt(var.com.HH.U.d),as.vector(eps.l))
        y.l<-exp(z.l) # y.l is in original scale
        
        AA<-y.l<t.d
        F0.t<-rowMeans(AA)
        
        B<-y.l
        B[which(B<0)]<-0
        BB<-((t.d-B)/t.d)*AA
        F1.t<-rowMeans(BB)
        
        CC<-((t.d-B)/t.d)^2*AA
        F2.t<-rowMeans(CC)
        
        FGT0<-sum(HH.Size.d*F0.t)/sum(HH.Size.d)
        FGT1<-sum(HH.Size.d*F1.t)/sum(HH.Size.d)
        FGT2<-sum(HH.Size.d*F2.t)/sum(HH.Size.d)
        
        list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
        
      }
      
    }
    
    F0.F11[d]<-apply(r.FGT$FGT0,2,mean)
    F0.F11.MSE[d]<-apply(r.FGT$FGT0,2,sd)
    F0.F11.Q.02.5[d]<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F0.F11.Q.97.5[d]<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
    F1.F11[d]<-apply(r.FGT$FGT1,2,mean)
    F1.F11.MSE[d]<-apply(r.FGT$FGT1,2,sd)
    F1.F11.Q.02.5[d]<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F1.F11.Q.97.5[d]<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
    F2.F11[d]<-apply(r.FGT$FGT2,2,mean)
    F2.F11.MSE[d]<-apply(r.FGT$FGT2,2,sd)
    F2.F11.Q.02.5[d]<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F2.F11.Q.97.5[d]<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
  }
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
}
# ------------------------------------------------------------------------------
CD.SM.HT.3L.FGT.Estimator.Scale<-function(beta,var.beta,jeta.s,eta.s,eps.s,var.com.3,var.com.2,var.com.1,var.com.HH.s,var.com.HH.U,ID.D,ID.C,ID.HH,X.U,t,HH.Size,No.Boot,residual.1=c("Fixed","Random")){
  
  # CD estimator for both Homogeneous variance component
  # 2nd level Residuals are scaled
  # t is here a value but need to be a vector
  # var.com.1 and var.com.1.U are scalar for scaling
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  No.Area<-length(unique(ID.D))
  
  scale.3<-sqrt(var.com.3/(sum(jeta.s^2)/(length(jeta.s)-1)))
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  
  jeta.s.scl<-jeta.s*scale.3
  eta.s.scl<-eta.s*scale.2
  eps.s.scl<-eps.s*scale.1
  
  std.eps.s<-eps.s.scl/sqrt(var.com.HH.s)
  
  n<-length(eps.s)
  
  F0.F11<-rep(0,No.Area)
  F0.F11.MSE<-rep(0,No.Area)
  F0.F11.Q.02.5<-rep(0,No.Area)
  F0.F11.Q.97.5<-rep(0,No.Area)
  
  F1.F11<-rep(0,No.Area)
  F1.F11.MSE<-rep(0,No.Area)
  F1.F11.Q.02.5<-rep(0,No.Area)
  F1.F11.Q.97.5<-rep(0,No.Area)
  
  F2.F11<-rep(0,No.Area)
  F2.F11.MSE<-rep(0,No.Area)
  F2.F11.Q.02.5<-rep(0,No.Area)
  F2.F11.Q.97.5<-rep(0,No.Area)
  
  for (d in 1:No.Area){
    
    cat(date(),"Iteration number",d,"starting","\n",fill=T)
    
    N.d<-length(ID.D[ID.D==d])
    N.c<-as.vector(table(ID.C[ID.D==d])) # sum(N.c)
    Cluster.c<-length(N.c)
    X.U.d<-X.U[ID.HH[ID.D==d],]
    t.d<-t[ID.D==d]
    HH.Size.d<-HH.Size[ID.HH[ID.D==d]]
    var.com.HH.U.d<-var.com.HH.U[ID.HH[ID.D==d]]
    
    r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
      
      beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
      eta.l<-as.vector(sample(eta.s.scl,Cluster.c,replace=TRUE))
      jeta.l<-sample(jeta.s.scl,1,replace=TRUE)
      
      if (residual.1=="Fixed") eps.l<-as.vector(std.eps.s)
      if (residual.1=="Random") eps.l<-sample(as.vector(std.eps.s),n,replace=TRUE)
      
      if (is.null(HH.Size)) {
        
        z.l<-as.vector(cbind(rep(1,N.d),X.U.d)%*%t(beta.l))+rep(jeta.l,N.d)+rep(eta.l,N.c)+outer(sqrt(var.com.HH.U.d),as.vector(eps.l))
        y.l<-exp(z.l) # y.l is in original scale
        
        AA<-y.l<t.d
        F0.t<-rowMeans(AA)
        
        B<-y.l
        B[which(B<0)]<-0
        BB<-((t.d-B)/t.d)*AA
        F1.t<-rowMeans(BB)
        
        CC<-((t.d-B)/t.d)^2*AA
        F2.t<-rowMeans(CC)
        
        FGT0<-mean(F0.t)
        FGT1<-mean(F1.t)
        FGT2<-mean(F2.t)
        
        list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
      }
      
      if (! is.null(HH.Size)) {
        
        z.l<-as.vector(cbind(rep(1,N.d),X.U.d)%*%t(beta.l))+rep(jeta.l,N.d)+rep(eta.l,N.c)+outer(sqrt(var.com.HH.U.d),as.vector(eps.l))
        y.l<-exp(z.l) # y.l is in original scale
        
        AA<-y.l<t.d
        F0.t<-rowMeans(AA)
        
        B<-y.l
        B[which(B<0)]<-0
        BB<-((t.d-B)/t.d)*AA
        F1.t<-rowMeans(BB)
        
        CC<-((t.d-B)/t.d)^2*AA
        F2.t<-rowMeans(CC)
        
        FGT0<-sum(HH.Size.d*F0.t)/sum(HH.Size.d)
        FGT1<-sum(HH.Size.d*F1.t)/sum(HH.Size.d)
        FGT2<-sum(HH.Size.d*F2.t)/sum(HH.Size.d)
        
        list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
        
      }
      
    }
    
    F0.F11[d]<-apply(r.FGT$FGT0,2,mean)
    F0.F11.MSE[d]<-apply(r.FGT$FGT0,2,sd)
    F0.F11.Q.02.5[d]<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F0.F11.Q.97.5[d]<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
    F1.F11[d]<-apply(r.FGT$FGT1,2,mean)
    F1.F11.MSE[d]<-apply(r.FGT$FGT1,2,sd)
    F1.F11.Q.02.5[d]<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F1.F11.Q.97.5[d]<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
    F2.F11[d]<-apply(r.FGT$FGT2,2,mean)
    F2.F11.MSE[d]<-apply(r.FGT$FGT2,2,sd)
    F2.F11.Q.02.5[d]<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F2.F11.Q.97.5[d]<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
  }
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
}
# ------------------------------------------------------------------------------
# Modified ELL: Modified ELL via parametric Bootstrap procedure: Homoskedasticity & Heteroskedasticity  
# ------------------------------------------------------------------------------
MELL.PB.HM.2L.FGT.Estimator<- function(beta,var.beta,var.com.1,Mod.var.com.2,NoClusterBlock,ID.D,ID.C,X.U,t,HH.Size,No.Boot){
  
  # This function is for estimating Distribution Function
  # Basic ELL Parametric method considering Homoskedastic Variance components
  # t is a value or a vector
  # Mod.var.com.2: Should be vector of length - number of Block
  # NoClusterBlock: Should be a vector of length - number of Block
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  NoBlock<-length(Mod.var.com.2)
  
  N<-length(ID.D)
  
  #  N.c<-as.vector(table(ID.C))
  #  C<-length(unique(ID.C))
  
  N.c<-as.vector(table(ID.C))[unique(ID.C)]
  C<-length(unique(ID.C))
  
  
  N.d<-as.vector(table(ID.D))[unique(ID.D)]
  D<-length(unique(ID.D))
  
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    
    adj.eta.l<-list()
    
    for(i in 1:NoBlock) adj.eta.l[[i]]<-rnorm(NoClusterBlock[i],0,sqrt(Mod.var.com.2[i]))
    
    eta.l<-c(unlist(adj.eta.l))
    eps.l<-rnorm(N,0,sqrt(var.com.1))
    
    if (is.null(X.U)) z.l<-cbind(rep(1,N))%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    if (! is.null(X.U)) z.l<-as.matrix(cbind(rep(1,N),X.U))%*%t(beta.l)+rep(eta.l,N.c)+eps.l # z.l is in logarithm scale
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
      
    }
    
    if (! is.null(HH.Size)) {
      
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
  
}
# ------------------------------------------------------------------------------
MELL.PB.HT.2L.FGT.Estimator<- function(beta,var.beta,alpha,var.alpha,sigma2.alpha,Mod.var.com.2,NoClusterBlock,ID.D,ID.C,X.U.HT,X.U,A,t,HH.Size,No.Boot){
  
  # This function is for estimating Distribution Function
  # Basic ELL Parametric method considering Homoskedastic Variance components
  # t is a value or a vector
  # Mod.var.com.2: Should be vector of length - number of Block
  # NoClusterBlock: Should be a vector of length - number of Block
  # Heteroskedastic error variances based on logistic function
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  N.d<-as.vector(table(ID.D))[unique(ID.D)]
  N.c<-as.vector(table(ID.C))[unique(ID.C)]
  C<-length(unique(ID.C))
  
  NoBlock<-length(Mod.var.com.2)
  
  # M2.eta.s<-u/sqrt(est.sigma2.2.HT)*sqrt(M2.est.sigma2.2)
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    alpha.l<-mvtnorm::rmvnorm(1,alpha,var.alpha)
    B <- exp(cbind(rep(1,N),X.U.HT)%*%t(alpha.l))
    var.com.HH.U <- A*B/(1+B) + 0.5*sigma2.alpha*(A*B)*(1-B)/((1+B)^3)
    
    adj.eta.l<-list()
    
    for(i in 1:NoBlock) adj.eta.l[[i]]<-rnorm(NoClusterBlock[i],0,sqrt(Mod.var.com.2[i]))
    
    eta.l<-c(unlist(adj.eta.l))
    eps.l<-rnorm(N,0,sqrt(var.com.HH.U))
    
    if (is.null(X.U)) z.l<-cbind(rep(1,N))%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    if (! is.null(X.U)) z.l<-as.matrix(cbind(rep(1,N),X.U))%*%t(beta.l)+rep(eta.l,N.c)+eps.l # z.l is in logarithm scale
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
}
# ------------------------------------------------------------------------------
# Modified ELL: Modified ELL via Non/Semi-parametric Bootstrap procedure: Homoskedasticity & Heteroskedasticity  
# ------------------------------------------------------------------------------
MELL.NPB.HM.2L.FGT.Estimator<- function(beta,var.beta,eta.s,eps.s,var.com.1,var.com.2,Mod.var.com.2,NoClusterBlock,ID.C.s,ID.D,ID.C,X.U,t,HH.Size,No.Boot,residual.1=c("unconditional","conditional")){
  
  # Non-parametric Bootstrap procedure (ELL, 2002,2003)
  # This function is for estimating Poverty Indicators
  # Heteroskedastic error variances based on logistic function
  # t is here a value but need to be a vector
  # Conditional: Draw individual level effects for a population cluster from the sample cluster whose random effect is randomly drawn for the population cluster
  # Unconditional: Draw without restriction of drawing cluster random effects
  # eta.s should be ordered in ID.C.s
  # eps.s and sig2.eps.s should be ordered in ID.C.s
  # Sample and population data sets should be ordered by area and clusters
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  N.d<-as.vector(table(ID.D))[unique(ID.D)]
  N.c<-as.vector(table(ID.C))[unique(ID.C)]
  C<-length(unique(ID.C))
  # standardized the residuals using the individual specific residuals
  
  # eps.std<-eps.s/sqrt(sig2.eps.s)-mean(eps.s/sqrt(sig2.eps.s))
  
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  eta.s.scl<-eta.s*scale.2
  
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  eps.s.scl<-eps.s*scale.1
  
  # M2.eta.s<-u/sqrt(est.sigma2.2.HT)*sqrt(M2.est.sigma2.2)
  
  NoBlock<-length(Mod.var.com.2)
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    
    if (residual.1=="unconditional") {
      
      adj.eta.l<-list()
      
      #for(i in 1:NoBlock) adj.eta.l[[i]]<-sample(eta.s/sqrt(var.com.2)*sqrt(Mod.var.com.2[i]),NoClusterBlock[i],replace=TRUE)
      for(i in 1:NoBlock) adj.eta.l[[i]]<-sample(eta.s.scl/sqrt(var.com.2)*sqrt(Mod.var.com.2[i]),NoClusterBlock[i],replace=TRUE)
      
      eta.l<-c(unlist(adj.eta.l))
      eps.l<-sample(eps.s.scl,N,replace=TRUE)
    }
    
    if (residual.1=="conditional") {
      
      adj.eta.l<-list()
      
      ID.C.sampling<-sample(c(1:length(unique(ID.C.s))),C,replace=TRUE)
      eta.l.origin<-eta.s.scl[ID.C.sampling]
      
      for(i in 1:NoBlock) adj.eta.l[[i]]<-sample(eta.l.origin/sqrt(var.com.2)*sqrt(Mod.var.com.2[i]),NoClusterBlock[i],replace=TRUE)
      eta.l<-c(unlist(adj.eta.l))
      
      ID.C.sampled<-unique(ID.C.s)[ID.C.sampling]
      
      eps.l<-NULL
      for (c in 1:C){
        eps.U<-sample(eps.s.scl[ID.C.s==ID.C.sampled[c]],N.c[c],replace=TRUE)
        eps.l<-c(eps.l,eps.U)
      }
      
    }
    
    z.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
}
# ------------------------------------------------------------------------------
MELL.NPB.HT.2L.FGT.Estimator.Scale<- function(beta,var.beta,alpha,var.alpha,sigma2.alpha,eta.s,var.com.2,var.com.1,Mod.var.com.2,NoClusterBlock,eps.s,sig2.eps.s,ID.C.s,ID.D,ID.C,X.U.HT,X.U,A,t,HH.Size,No.Boot,residual.1=c("unconditional","conditional")){
  
  # Non-parametric Bootstrap procedure (ELL, 2002,2003)
  # This function is for estimating Distribution function
  # Heteroskedastic error variances based on logistic function
  # t is here a value but need to be a vector
  # Conditional: Draw individual level effects for a population cluster from the sample cluster whose random effect is randomly drawn for the population cluster
  # Unconditional: Draw without restriction of drawing cluster random effects
  # eta.s should be ordered in ID.C.s
  # eps.s and sig2.eps.s should be ordered in ID.C.s
  # Sample and population data sets should be ordered by area and clusters
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  N.d<-as.vector(table(ID.D))[unique(ID.D)]
  N.c<-as.vector(table(ID.C))[unique(ID.C)]
  C<-length(unique(ID.C))
  
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  eta.s.scl<-eta.s*scale.2
  
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  eps.s.scl<-eps.s*scale.1
  
  # standardized the residuals using the individual specific residuals
  eps.std<-eps.s.scl/sqrt(sig2.eps.s)-mean(eps.s.scl/sqrt(sig2.eps.s))
  
  # M2.eta.s<-u/sqrt(est.sigma2.2.HT)*sqrt(M2.est.sigma2.2)
  
  NoBlock<-length(Mod.var.com.2)
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    alpha.l<-mvtnorm::rmvnorm(1,alpha,var.alpha)
    B <- exp(cbind(rep(1,N),X.U.HT)%*%t(alpha.l))
    var.com.HH.U <- A*B/(1+B) + 0.5*sigma2.alpha*(A*B)*(1-B)/((1+B)^3)
    
    if (residual.1=="unconditional") {
      
      adj.eta.l<-list()
      
      for(i in 1:NoBlock) adj.eta.l[[i]]<-sample(eta.s.scl/sqrt(var.com.2)*sqrt(Mod.var.com.2[i]),NoClusterBlock[i],replace=TRUE)
      eta.l<-c(unlist(adj.eta.l))
      eps.u.std<-sample(eps.std,N,replace=TRUE)
    }
    
    if (residual.1=="conditional") {
      
      ID.C.sampling<-sample(c(1:length(unique(ID.C.s))),C,replace=TRUE)
      eta.l.origin<-eta.s.scl[ID.C.sampling]
      
      adj.eta.l<-list()
      
      for(i in 1:NoBlock) adj.eta.l[[i]]<-sample(eta.l.origin/sqrt(var.com.2)*sqrt(Mod.var.com.2[i]),NoClusterBlock[i],replace=TRUE)
      eta.l<-c(unlist(adj.eta.l))
      
      ID.C.sampled<-unique(ID.C.s)[ID.C.sampling]
      
      eps.u.std<-NULL
      for (c in 1:C){
        eps.U<-sample(eps.std[ID.C.s==ID.C.sampled[c]],N.c[c],replace=TRUE)
        eps.u.std<-c(eps.u.std,eps.U)
      }
      
    }
    
    eps.l<-eps.u.std*sqrt(var.com.HH.U)
    
    if (is.null(X.U)) z.l<-cbind(rep(1,N))%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    if (! is.null(X.U)) z.l<-as.matrix(cbind(rep(1,N),X.U))%*%t(beta.l)+rep(eta.l,N.c)+eps.l # z.l is in logarithm scale
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
}
# ------------------------------------------------------------------------------
# Modified CDMC: Modified CD method via MC simulation approach and Non-parametric Bootstrap procedure: Homoskedasticity & Heteroskedasticity  
# ------------------------------------------------------------------------------
MCD.MC.HM.2L.FGT.Estimator<-function(beta,var.beta,eta.s,eps.s,var.com.2,var.com.1,Mod.var.com.2,NoClusterBlock,ID.C.s,ID.D,ID.C,X.U,t,HH.Size,No.Boot,residual.1=c("unconditional","conditional")){
  
  # Following the Marchetti et al (2012) as an alternative of CD approach
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  C<-length(unique(ID.C))
  N.c<-as.vector(table(ID.C))[unique(ID.C)]
  
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  
  eta.s.scl<-eta.s*scale.2
  eps.s.scl<-eps.s*scale.1
  
  NoBlock<-length(Mod.var.com.2)
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    
    if (residual.1=="unconditional") {
      
      adj.eta.l<-list()
      
      for(i in 1:NoBlock) adj.eta.l[[i]]<-sample(eta.s.scl/sqrt(var.com.2)*sqrt(Mod.var.com.2[i]),NoClusterBlock[i],replace=TRUE)
      
      eta.l<-c(unlist(adj.eta.l))
      eps.l<-sample(eps.s.scl,N,replace=TRUE)
      
    }
    
    if (residual.1=="conditional") {
      
      adj.eta.l<-list()
      
      ID.C.sampling<-sample(c(1:length(unique(ID.C.s))),C,replace=TRUE)
      eta.l.origin<-eta.s.scl[ID.C.sampling]
      
      for(i in 1:NoBlock) adj.eta.l[[i]]<-sample(eta.l.origin/sqrt(var.com.2)*sqrt(Mod.var.com.2[i]),NoClusterBlock[i],replace=TRUE)
      eta.l<-c(unlist(adj.eta.l))
      
      ID.C.sampled<-unique(ID.C.s)[ID.C.sampling]
      
      eps.l<-NULL
      for (c in 1:C){
        eps.U<-sample(eps.s.scl[ID.C.s==ID.C.sampled[c]],N.c[c],replace=TRUE)
        eps.l<-c(eps.l,eps.U)
      }
      
    }
    
    if (is.null(X.U))   z.l<-cbind(rep(1,N))%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    if (! is.null(X.U)) z.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    
    y.l<-exp(z.l) # y.l is in original scale
    
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
  
}
# ------------------------------------------------------------------------------
MCD.MC.HT.2L.FGT.Estimator.Scale<-function(beta,var.beta,eta.s,eps.s,var.com.2,var.com.1,Mod.var.com.2,NoClusterBlock,var.com.HH.s,var.com.HH.U,ID.C.s,ID.D,ID.C,X.U,t,HH.Size,No.Boot,residual.1=c("unconditional","conditional")){
  
  # Following the Marchetti et al (2012) as an alternative of CD approach
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  N<-length(ID.D)
  C<-length(unique(ID.C))
  N.c<-as.vector(table(ID.C))[unique(ID.C)]
  
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  eta.s.scl<-eta.s*scale.2
  
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  eps.s.scl<-eps.s*scale.1
  
  std.eps.s<-eps.s.scl/sqrt(var.com.HH.s) #-mean(eps.s/sqrt(var.com.HH.s))
  
  NoBlock<-length(Mod.var.com.2)
  
  r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
    
    beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
    
    #  eta.u<-sample(eta.s,C,replace=TRUE)
    #  eps.u.l<-sample(std.eps.s,N,replace=TRUE)
    
    if (residual.1=="unconditional") {
      #eta.l<-sample(eta.s,C,replace=TRUE)
      
      adj.eta.l<-list()
      for(i in 1:NoBlock) adj.eta.l[[i]]<-sample(eta.s.scl/sqrt(var.com.2)*sqrt(Mod.var.com.2[i]),NoClusterBlock[i],replace=TRUE)
      eta.l<-c(unlist(adj.eta.l))
      
      eps.u.std<-sample(std.eps.s,N,replace=TRUE)
    }
    
    if (residual.1=="conditional") {
      
      adj.eta.l<-list()
      
      ID.C.sampling<-sample(c(1:length(unique(ID.C.s))),C,replace=TRUE)
      eta.l.origin<-eta.s.scl[ID.C.sampling]
      
      for(i in 1:NoBlock) adj.eta.l[[i]]<-sample(eta.l.origin/sqrt(var.com.2)*sqrt(Mod.var.com.2[i]),NoClusterBlock[i],replace=TRUE)
      eta.l<-c(unlist(adj.eta.l))
      
      ID.C.sampled<-unique(ID.C.s)[ID.C.sampling]
      
      eps.u.std<-NULL
      for (c in 1:C){
        eps.U<-sample(std.eps.s[ID.C.s==ID.C.sampled[c]],N.c[c],replace=TRUE)
        eps.u.std<-c(eps.u.std,eps.U)
      }
      
    }
    
    eps.l<- eps.u.std*sqrt(var.com.HH.U)
    
    if (is.null(X.U))   z.l<-cbind(rep(1,N))%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    if (! is.null(X.U)) z.l<-cbind(rep(1,N),X.U)%*%t(beta.l)+rep(eta.l,N.c)+eps.l
    
    y.l<-exp(z.l) # y.l is in original scale
    
    if (is.null(HH.Size)) {
      index.0<-ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,mean)
      FGT1<-tapply(index.1,ID.D,mean)
      FGT2<-tapply(index.2,ID.D,mean)
    }
    
    if (! is.null(HH.Size)) {
      index.0<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^0
      index.1<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^1
      index.2<-HH.Size*ifelse(y.l<t,1,0)*((t-y.l)/t)^2
      
      FGT0<-tapply(index.0,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT1<-tapply(index.1,ID.D,sum)/tapply(HH.Size,ID.D,sum)
      FGT2<-tapply(index.2,ID.D,sum)/tapply(HH.Size,ID.D,sum)
    }
    
    list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
  }
  
  F0.F11<-colMeans(r.FGT$FGT0)
  F0.F11.MSE<-apply(r.FGT$FGT0,2,sd)
  F0.F11.Q.02.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F0.F11.Q.97.5<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F1.F11<-colMeans(r.FGT$FGT1)
  F1.F11.MSE<-apply(r.FGT$FGT1,2,sd)
  F1.F11.Q.02.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F1.F11.Q.97.5<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  F2.F11<-colMeans(r.FGT$FGT2)
  F2.F11.MSE<-apply(r.FGT$FGT2,2,sd)
  F2.F11.Q.02.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
  F2.F11.Q.97.5<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
  
}
# ------------------------------------------------------------------------------
# Modified CDSM: Modified CD method via SM approach with non-parametric Bootstrap procedure: Homoskedasticity & Heteroskedasticity  
# ------------------------------------------------------------------------------
MCD.SM.HM.2L.FGT.Estimator<-function(beta,var.beta,eta.s,eps.s,var.com.2,var.com.1,Mod.var.com.2,NoClusterBlock,Stratum,ID.D,ID.C,ID.HH,X.U,t,HH.Size,No.Boot,residual.1=c("Fixed","Random")){
  
  # CD estimator for both Homogeneous variance component
  # 2nd level Residuals are scaled
  # t is here a value but need to be a vector
  # var.com.1 and var.com.1.U are scalar for scaling
  # Population will be sorted according to Stratum , Area, Cluster , HH
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  No.Area<-length(unique(ID.D))
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  
  eta.s.scl<-eta.s*scale.2
  eps.s.scl<-eps.s*scale.1
  std.eps.s<-eps.s.scl/sqrt(var.com.1)
  
  NoBlock<-length(Mod.var.com.2)
  
  n<-length(eps.s)
  
  Mod.var.com.2.Area<-NULL
  for (d in 1:No.Area) Mod.var.com.2.Area<-c(Mod.var.com.2.Area,Mod.var.com.2[unique(Stratum[ID.D==d])])
  
  
  F0.F11<-rep(0,No.Area)
  F0.F11.MSE<-rep(0,No.Area)
  F0.F11.Q.02.5<-rep(0,No.Area)
  F0.F11.Q.97.5<-rep(0,No.Area)
  
  F1.F11<-rep(0,No.Area)
  F1.F11.MSE<-rep(0,No.Area)
  F1.F11.Q.02.5<-rep(0,No.Area)
  F1.F11.Q.97.5<-rep(0,No.Area)
  
  F2.F11<-rep(0,No.Area)
  F2.F11.MSE<-rep(0,No.Area)
  F2.F11.Q.02.5<-rep(0,No.Area)
  F2.F11.Q.97.5<-rep(0,No.Area)
  
  
  for (d in 1:No.Area){
    
    cat(date(),"Iteration number",d,"starting","\n",fill=T)
    
    N.d<-length(ID.D[ID.D==d])
    N.c<-as.vector(table(ID.C[ID.D==d])) # sum(N.c)
    Cluster.c<-length(N.c)
    X.U.d<-X.U[ID.HH[ID.D==d],]
    t.d<-t[ID.D==d]
    HH.Size.d<-HH.Size[ID.D==d]
    
    
    
    r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
      
      beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
      
      #adj.eta.l<-list()
      #for(i in 1:NoBlock) adj.eta.l[[i]]<-sample(eta.s.scl/sqrt(var.com.2)*sqrt(Mod.var.com.2[i]),NoClusterBlock[i],replace=TRUE)
      #eta.l<-c(unlist(adj.eta.l))
      
      eta.l<-sample(eta.s.scl/sqrt(var.com.2)*sqrt(Mod.var.com.2.Area[d]),Cluster.c,replace=TRUE)
      #eta.l<-as.vector(sample(eta.u.scl,Cluster.c,replace=TRUE))
      
      if (residual.1=="Fixed") eps.l<-as.vector(std.eps.s)
      if (residual.1=="Random") eps.l<-sample(as.vector(std.eps.s),n,replace=TRUE)
      
      if (is.null(HH.Size)) {
        
        z.l<-as.vector(cbind(rep(1,N.d))%*%t(beta.l))+rep(eta.l,N.c)+outer(sqrt(rep(var.com.1,N.d)),as.vector(eps.l))
        y.l<-exp(z.l) # y.l is in original scale
        
        AA<-y.l<t.d
        F0.t<-rowMeans(AA)
        
        B<-y.l
        B[which(B<0)]<-0
        BB<-((t.d-B)/t.d)*AA
        F1.t<-rowMeans(BB)
        
        CC<-((t.d-B)/t.d)^2*AA
        F2.t<-rowMeans(CC)
        
        FGT0<-mean(F0.t)
        FGT1<-mean(F1.t)
        FGT2<-mean(F2.t)
        
        list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
        
      }
      
      if (! is.null(HH.Size)) {
        
        z.l<-as.vector(cbind(rep(1,N.d),X.U.d)%*%t(beta.l))+rep(eta.l,N.c)+outer(sqrt(rep(var.com.1,N.d)),as.vector(eps.l))
        y.l<-exp(z.l) # y.l is in original scale
        
        AA<-y.l<t.d
        F0.t<-rowMeans(AA)
        
        B<-y.l
        B[which(B<0)]<-0
        BB<-((t.d-B)/t.d)*AA
        F1.t<-rowMeans(BB)
        
        CC<-((t.d-B)/t.d)^2*AA
        F2.t<-rowMeans(CC)
        
        FGT0<-sum(HH.Size.d*F0.t)/sum(HH.Size.d)
        FGT1<-sum(HH.Size.d*F1.t)/sum(HH.Size.d)
        FGT2<-sum(HH.Size.d*F2.t)/sum(HH.Size.d)
        
        list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
      }
      
    }
    
    F0.F11[d]<-apply(r.FGT$FGT0,2,mean)
    F0.F11.MSE[d]<-apply(r.FGT$FGT0,2,sd)
    F0.F11.Q.02.5[d]<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F0.F11.Q.97.5[d]<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
    F1.F11[d]<-apply(r.FGT$FGT1,2,mean)
    F1.F11.MSE[d]<-apply(r.FGT$FGT1,2,sd)
    F1.F11.Q.02.5[d]<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F1.F11.Q.97.5[d]<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
    F2.F11[d]<-apply(r.FGT$FGT2,2,mean)
    F2.F11.MSE[d]<-apply(r.FGT$FGT2,2,sd)
    F2.F11.Q.02.5[d]<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F2.F11.Q.97.5[d]<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
  }
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
}
# ------------------------------------------------------------------------------
MCD.SM.HT.2L.FGT.Estimator.Scale<-function(beta,var.beta,eta.s,eps.s,var.com.2,var.com.1,Mod.var.com.2,NoClusterBlock,var.com.HH.s,var.com.HH.U,Stratum,ID.D,ID.C,ID.HH,X.U,t,HH.Size,No.Boot,residual.1=c("Fixed","Random")){
  
  # CD estimator for both Homogeneous variance component
  # 2nd level Residuals are scaled
  # t is here a value but need to be a vector
  # var.com.1 and var.com.1.U are scalar for scaling
  
  f2 <- function(obj1,obj2) {
    # f2 is for single quantile
    z <- list(
      FGT0=rbind(obj1$FGT0,obj2$FGT0),
      FGT1=rbind(obj1$FGT1,obj2$FGT1),
      FGT2=rbind(obj1$FGT2,obj2$FGT2)
    )
  }
  
  No.Area<-length(unique(ID.D))
  
  scale.2<-sqrt(var.com.2/(sum(eta.s^2)/(length(eta.s)-1)))
  scale.1<-sqrt(var.com.1/(sum(eps.s^2)/(length(eps.s)-1)))
  
  eta.s.scl<-eta.s*scale.2
  eps.s.scl<-eps.s*scale.1
  
  std.eps.s<-eps.s.scl/sqrt(var.com.HH.s)
  
  n<-length(eps.s)
  
  NoBlock<-length(Mod.var.com.2)
  
  Mod.var.com.2.Area<-NULL
  for (d in 1:No.Area) Mod.var.com.2.Area<-c(Mod.var.com.2.Area,Mod.var.com.2[unique(Stratum[ID.D==d])])
  
  F0.F11<-rep(0,No.Area)
  F0.F11.MSE<-rep(0,No.Area)
  F0.F11.Q.02.5<-rep(0,No.Area)
  F0.F11.Q.97.5<-rep(0,No.Area)
  
  F1.F11<-rep(0,No.Area)
  F1.F11.MSE<-rep(0,No.Area)
  F1.F11.Q.02.5<-rep(0,No.Area)
  F1.F11.Q.97.5<-rep(0,No.Area)
  
  F2.F11<-rep(0,No.Area)
  F2.F11.MSE<-rep(0,No.Area)
  F2.F11.Q.02.5<-rep(0,No.Area)
  F2.F11.Q.97.5<-rep(0,No.Area)
  
  for (d in 1:No.Area){
    
    cat(date(),"Iteration number",d,"starting","\n",fill=T)
    
    N.d<-length(ID.D[ID.D==d])
    N.c<-as.vector(table(ID.C[ID.D==d])) # sum(N.c)
    Cluster.c<-length(N.c)
    X.U.d<-X.U[ID.HH[ID.D==d],]
    t.d<-t[ID.D==d]
    HH.Size.d<-HH.Size[ID.HH[ID.D==d]]
    var.com.HH.U.d<-var.com.HH.U[ID.HH[ID.D==d]]
    
    r.FGT <- foreach(icount(No.Boot), .combine=f2) %dopar% {
      
      beta.l<-mvtnorm::rmvnorm(1,beta,var.beta)
      #eta.l<-as.vector(sample(eta.s,Cluster.c,replace=TRUE))
      
      #adj.eta.l<-list()
      #for(i in 1:NoBlock) adj.eta.l[[i]]<-sample(eta.s.scl/sqrt(var.com.2)*sqrt(Mod.var.com.2[i]),NoClusterBlock[i],replace=TRUE)
      #eta.l<-c(unlist(adj.eta.l))
      
      eta.l<-sample(eta.s.scl/sqrt(var.com.2)*sqrt(Mod.var.com.2.Area[d]),Cluster.c,replace=TRUE)
      
      if (residual.1=="Fixed") eps.l<-as.vector(std.eps.s)
      if (residual.1=="Random") eps.l<-sample(as.vector(std.eps.s),n,replace=TRUE)
      
      if (is.null(HH.Size)) {
        
        z.l<-as.vector(cbind(rep(1,N.d),X.U.d)%*%t(beta.l))+rep(eta.l,N.c)+outer(sqrt(var.com.HH.U.d),as.vector(eps.l))
        y.l<-exp(z.l) # y.l is in original scale
        
        AA<-y.l<t.d
        F0.t<-rowMeans(AA)
        
        B<-y.l
        B[which(B<0)]<-0
        BB<-((t.d-B)/t.d)*AA
        F1.t<-rowMeans(BB)
        
        CC<-((t.d-B)/t.d)^2*AA
        F2.t<-rowMeans(CC)
        
        FGT0<-mean(F0.t)
        FGT1<-mean(F1.t)
        FGT2<-mean(F2.t)
        
        list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
      }
      
      if (! is.null(HH.Size)) {
        
        z.l<-as.vector(cbind(rep(1,N.d),X.U.d)%*%t(beta.l))+rep(eta.l,N.c)+outer(sqrt(var.com.HH.U.d),as.vector(eps.l))
        y.l<-exp(z.l) # y.l is in original scale
        
        AA<-y.l<t.d
        F0.t<-rowMeans(AA)
        
        B<-y.l
        B[which(B<0)]<-0
        BB<-((t.d-B)/t.d)*AA
        F1.t<-rowMeans(BB)
        
        CC<-((t.d-B)/t.d)^2*AA
        F2.t<-rowMeans(CC)
        
        FGT0<-sum(HH.Size.d*F0.t)/sum(HH.Size.d)
        FGT1<-sum(HH.Size.d*F1.t)/sum(HH.Size.d)
        FGT2<-sum(HH.Size.d*F2.t)/sum(HH.Size.d)
        
        list(FGT0=FGT0,FGT1=FGT1,FGT2=FGT2)
        
      }
      
    }
    
    F0.F11[d]<-apply(r.FGT$FGT0,2,mean)
    F0.F11.MSE[d]<-apply(r.FGT$FGT0,2,sd)
    F0.F11.Q.02.5[d]<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F0.F11.Q.97.5[d]<-apply(r.FGT$FGT0,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
    F1.F11[d]<-apply(r.FGT$FGT1,2,mean)
    F1.F11.MSE[d]<-apply(r.FGT$FGT1,2,sd)
    F1.F11.Q.02.5[d]<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F1.F11.Q.97.5[d]<-apply(r.FGT$FGT1,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
    F2.F11[d]<-apply(r.FGT$FGT2,2,mean)
    F2.F11.MSE[d]<-apply(r.FGT$FGT2,2,sd)
    F2.F11.Q.02.5[d]<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.025,na.rm=TRUE))
    F2.F11.Q.97.5[d]<-apply(r.FGT$FGT2,2,function(x) quantile(x,0.975,na.rm=TRUE))
    
  }
  
  list(F0.F11=F0.F11,F0.F11.MSE=F0.F11.MSE,F0.F11.Q.02.5=F0.F11.Q.02.5,F0.F11.Q.97.5=F0.F11.Q.97.5,
       F1.F11=F1.F11,F1.F11.MSE=F1.F11.MSE,F1.F11.Q.02.5=F1.F11.Q.02.5,F1.F11.Q.97.5=F1.F11.Q.97.5,
       F2.F11=F2.F11,F2.F11.MSE=F2.F11.MSE,F2.F11.Q.02.5=F2.F11.Q.02.5,F2.F11.Q.97.5=F2.F11.Q.97.5)
}

# ------------------------------------------------------------------------------
# Bangladesh Datasets
# ------------------------------------------------------------------------------
load("Thesis R Script/Census.data.Rdata")
load("Thesis R Script/Survey.data.Rdata")
# ------------------------------------------------------------------------------
# Population and Sample Data structure
# ------------------------------------------------------------------------------
N.Area<-tapply.order(Census.data.fitted$hhold,Census.data.fitted$ID.UPZ,length,unique(Census.data.fitted$ID.UPZ))
N.Cluster<-tapply.order(Census.data.fitted$hhold,Census.data.fitted$psu,length,unique(Census.data.fitted$psu))
No.Area<-length(N.Area)
No.Cluster<-length(N.Cluster)
N<-sum(N.Area)
No.PP.Area.U<-tapply.order(Census.data.fitted$HH.size.U,Census.data.fitted$ID.UPZ,sum,unique(Census.data.fitted$ID.UPZ))
Census.data.fitted$HH.ID<-c(1:N)
Census.data.fitted$PSU.ID<-rep(c(1:No.Cluster),N.Cluster)
Census.data.fitted$AREA.ID<-rep(c(1:No.Area),N.Area)
No.Cluster.s<-length(unique(sample.data.fitted$psu))
n<-length(sample.data.fitted$ln_p_expnd)
n.i<-tapply.order(sample.data.fitted$ln_p_expnd,sample.data.fitted$ID.UPZ,length,unique(sample.data.fitted$ID.UPZ))
n.ij<-tapply.order(sample.data.fitted$ln_p_expnd,sample.data.fitted$psu,length,unique(sample.data.fitted$psu))
No.Area.s<-length(n.i)
sample.data.fitted$HH.ID<-c(1:n)
sample.data.fitted$PSU.ID<-rep(c(1:No.Cluster.s),n.ij)
sample.data.fitted$AREA.ID<-rep(c(1:No.Area.s),n.i)
# ------------------------------------------------------------------------------
# Matrix of Explanatory Variables from population and Survey data sets
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
x.matrix.s<-data.frame(sample.data.fitted$electric,sample.data.fitted$ilattr_1,sample.data.fitted$ilattr_3,sample.data.fitted$iwater1,sample.data.fitted$ibuild_3,sample.data.fitted$rural,
                       sample.data.fitted$owner,sample.data.fitted$ibuild_4,sample.data.fitted$workst2p,sample.data.fitted$workst3p,sample.data.fitted$iincom_3,
                       sample.data.fitted$num_hh,sample.data.fitted$num_hh2,sample.data.fitted$hhhprmed,sample.data.fitted$literatep,sample.data.fitted$child5p,
                       sample.data.fitted$mhhsize,sample.data.fitted$depratio,sample.data.fitted$paginc,sample.data.fitted$idiv_1,
                       sample.data.fitted$idiv_7,sample.data.fitted$idiv_4,sample.data.fitted$idiv_5,sample.data.fitted$femalep.rural,
                       sample.data.fitted$ibuild_3*sample.data.fitted$rural,sample.data.fitted$owner*sample.data.fitted$ibuild_4,
                       sample.data.fitted$workst3p*sample.data.fitted$rural,sample.data.fitted$num_hh*sample.data.fitted$rural,
                       sample.data.fitted$num_hh2*sample.data.fitted$rural,sample.data.fitted$hhhprmed*sample.data.fitted$rural)
dim(x.matrix.s)
Census.data.fitted<-Census.data.fitted[order(Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]
x.matrix.U<-data.frame(Census.data.fitted$electric,Census.data.fitted$ilattr_1,Census.data.fitted$ilattr_3,Census.data.fitted$iwater1,Census.data.fitted$ibuild_3,Census.data.fitted$rural,
                       Census.data.fitted$owner,Census.data.fitted$ibuild_4,Census.data.fitted$workst2p,Census.data.fitted$workst3p,Census.data.fitted$iincom_3,
                       Census.data.fitted$num_hh,Census.data.fitted$num_hh2,Census.data.fitted$hhhprmed,Census.data.fitted$literatep,Census.data.fitted$child5p,
                       Census.data.fitted$mhhsize,Census.data.fitted$depratio,Census.data.fitted$paginc,Census.data.fitted$idiv_1,
                       Census.data.fitted$idiv_7,Census.data.fitted$idiv_4,Census.data.fitted$idiv_5,Census.data.fitted$femalep.rural,
                       Census.data.fitted$ibuild_3*Census.data.fitted$rural,Census.data.fitted$owner*Census.data.fitted$ibuild_4,
                       Census.data.fitted$workst3p*Census.data.fitted$rural,Census.data.fitted$num_hh*Census.data.fitted$rural,
                       Census.data.fitted$num_hh2*Census.data.fitted$rural,Census.data.fitted$hhhprmed*Census.data.fitted$rural)
dim(x.matrix.U)
# ------------------------------------------------------------------------------
# Two-level model using GLS method assuming HM Nested errors 
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
ols.1<-lm(ln_p_expnd~electric+ilattr_1+ilattr_3+iwater1+ibuild_3*rural+owner*ibuild_4+workst2p+workst3p*rural+iincom_3+num_hh*rural+num_hh2*rural+hhhprmed*rural+literatep+child5p+mhhsize+depratio+paginc+idiv_1+idiv_7+idiv_4+idiv_5+femalep.rural,data=sample.data.fitted)
sample.data.fitted$u.ch<-resid(ols.1)
u<-tapply.order(sample.data.fitted$u.ch,sample.data.fitted$PSU.ID,mean,unique(sample.data.fitted$PSU.ID))
sample.data.fitted$u <- with(sample.data.fitted, ave(u.ch, PSU.ID, FUN=mean))
sample.data.fitted$eps.2<-sample.data.fitted$u.ch-sample.data.fitted$u # No application latter
sample.data.fitted$y.hat.2<-fitted.values(ols.1)
est.sigma2.2<-Var.Com.MM.2(sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID,u,sample.data.fitted$u.ch)
est.sigma2.2$sigma2.2/(est.sigma2.2$sigma2.2+est.sigma2.2$sigma2.1)
X.ols<-model.matrix(ols.1)
gls.lm2<-GLS.EST.2L(sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID,est.sigma2.2$sigma2.2,est.sigma2.2$sigma2.1,x.matrix=X.ols,sample.data.fitted$ln_p_expnd)
beta.gls.2<-gls.lm2$beta.gls
var.beta.gls.2<-gls.lm2$vcov.beta.gls
t.beta.gls.2<-beta.gls.2/sqrt(diag(var.beta.gls.2))
p.beta.gls.2<-2*(1-pt(abs(t.beta.gls.2),n-length(beta.gls.2)))
coef.table.beta.gls.2<-round(data.frame(beta.gls.2=beta.gls.2,SE=sqrt(diag(var.beta.gls.2)),t=t.beta.gls.2,prob=p.beta.gls.2),5)
R2.gls.lm2.M<-rsquared.lmm.mom(beta.gls.2,X.ols,est.sigma2.2)$R.squared.M
R2.gls.lm2.C<-rsquared.lmm.mom(beta.gls.2,X.ols,est.sigma2.2)$R.squared.C
sample.data.fitted$y.hat.gls.2<-X.ols%*%beta.gls.2
sample.data.fitted$u.ch.gls.2<-sample.data.fitted$ln_p_expnd-sample.data.fitted$y.hat.gls.2
sample.data.fitted$u.gls.2<-with(sample.data.fitted, ave(u.ch.gls.2, PSU.ID, FUN=mean))
sample.data.fitted$eps.gls.2<-sample.data.fitted$u.ch.gls.2-sample.data.fitted$u.gls.2
u.gls.2<-tapply.order(sample.data.fitted$u.ch.gls.2,sample.data.fitted$PSU.ID,mean,unique(sample.data.fitted$PSU.ID))
# ------------------------------------------------------------------------------
# Three-level model using GLS method assuming HM Nested errors 
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
u<-tapply.order(sample.data.fitted$u.ch,sample.data.fitted$PSU.ID,mean,unique(sample.data.fitted$PSU.ID))
sample.data.fitted$u <- with(sample.data.fitted, ave(u.ch, PSU.ID, FUN=mean))
eta<-tapply.order(sample.data.fitted$u.ch,sample.data.fitted$AREA.ID,mean,unique(sample.data.fitted$AREA.ID))
sample.data.fitted$eta<-with(sample.data.fitted, ave(u.ch, AREA.ID, FUN=mean))
sample.data.fitted$eps.3<-sample.data.fitted$u.ch-sample.data.fitted$u-sample.data.fitted$eta # No application latter
est.sigma2.3<-Var.Com.MM.3(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID,eta,u,sample.data.fitted$u.ch)
est.sigma2.3$sigma2.3/(est.sigma2.3$sigma2.3+est.sigma2.3$sigma2.2+est.sigma2.3$sigma2.1)
est.sigma2.3$sigma2.2/(est.sigma2.3$sigma2.3+est.sigma2.3$sigma2.2+est.sigma2.3$sigma2.1)
gls.lm3<-GLS.EST.3L(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID,est.sigma2.3$sigma2.3,est.sigma2.3$sigma2.2,est.sigma2.3$sigma2.1,x.matrix=X.ols,sample.data.fitted$ln_p_expnd)
beta.gls.3<-gls.lm3$beta.gls
var.beta.gls.3<-gls.lm3$vcov.beta.gls
t.beta.gls.3<-beta.gls.3/sqrt(diag(var.beta.gls.3))
p.beta.gls.3<-2*(1-pt(abs(t.beta.gls.3),n-length(beta.gls.3)))
coef.table.beta.gls.3<-round(data.frame(beta.gls.3=beta.gls.3,SE=sqrt(diag(var.beta.gls.3)),t=t.beta.gls.3,prob=p.beta.gls.3),5)
R2.gls.lm3.M<-rsquared.lmm.mom(beta.gls.2,X.ols,est.sigma2.3)$R.squared.M
R2.gls.lm3.C<-rsquared.lmm.mom(beta.gls.2,X.ols,est.sigma2.3)$R.squared.C
sample.data.fitted$y.hat.gls.3<-X.ols%*%beta.gls.3
sample.data.fitted$u.ch.gls.3<-sample.data.fitted$ln_p_expnd-sample.data.fitted$y.hat.gls.3
sample.data.fitted$u.gls.3<-with(sample.data.fitted, ave(u.ch.gls.3, PSU.ID, FUN=mean))
sample.data.fitted$eta.gls.3<-with(sample.data.fitted, ave(u.ch.gls.3, AREA.ID, FUN=mean))
sample.data.fitted$eps.gls.3<-sample.data.fitted$u.ch.gls.3-sample.data.fitted$eta.gls.3-sample.data.fitted$u.gls.3
u.gls.3<-tapply.order(sample.data.fitted$u.ch.gls.2,sample.data.fitted$PSU.ID,mean,unique(sample.data.fitted$PSU.ID))
eta.gls.3<-tapply.order(sample.data.fitted$u.ch.gls.2,sample.data.fitted$AREA.ID,mean,unique(sample.data.fitted$AREA.ID))
# ------------------------------------------------------------------------------
# Implementation of Parametric ELL Methodology: Homoskedasticity
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted<-Census.data.fitted[order(Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]
# ------------------------------------------------------------------------------
# 2L model: Homoskedasticity
# ------------------------------------------------------------------------------
set.seed(2015)
ELL.PB.2L.HM.FGT.Estimate.PP.UPOVLN<-ELL.PB.HM.2L.FGT.Estimator(beta=beta.gls.2,var.beta=var.beta.gls.2,var.com.1=est.sigma2.2$sigma2.1,var.com.2=est.sigma2.2$sigma2.2,
                                                                ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,X.U=as.matrix(x.matrix.U),t=Census.data.fitted$upovln,
                                                              HH.Size=Census.data.fitted$HH.size.U,No.Boot=5)
# ------------------------------------------------------------------------------
# 3L model: Homoskedasticity
# ------------------------------------------------------------------------------
set.seed(2015)
ELL.PB.3L.FGT.Estimate.PP.UPOVLN<-ELL.PB.HM.3L.FGT.Estimator(beta=beta.gls.3,var.beta=var.beta.gls.3,var.com.1=est.sigma2.3$sigma2.1,var.com.2=est.sigma2.3$sigma2.2,
                                                             var.com.3=est.sigma2.3$sigma2.3,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,X.U=x.matrix.U,t=Census.data.fitted$upovln,
                                                             HH.Size=Census.data.fitted$HH.size.U,No.Boot=5)
# ------------------------------------------------------------------------------
# Implementation of Non-parametric ELL Methodology: Homoskedasticity
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted<-Census.data.fitted[order(Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]
# ------------------------------------------------------------------------------
# 2L model: Homoskedasticity
# ------------------------------------------------------------------------------
set.seed(2015)
NPELL.HM.2L.FGT.Estimate.UNC.UPOVLN<-ELL.NPB.HM.2L.FGT.Estimator.Scale(beta=beta.gls.2,var.beta=var.beta.gls.2,eta.s=u,eps.s=sample.data.fitted$eps.2,
                                                                       var.com.1=est.sigma2.2$sigma2.1,var.com.2=est.sigma2.2$sigma2.2,
                                                                       ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                                       X.U=as.matrix(x.matrix.U),t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("unconditional"))

set.seed(2015)
NPELL.HM.2L.FGT.Estimate.CON.UPOVLN<-ELL.NPB.HM.2L.FGT.Estimator.Scale(beta=beta.gls.2,var.beta=var.beta.gls.2,eta.s=u,eps.s=sample.data.fitted$eps.2,
                                                                       var.com.1=est.sigma2.2$sigma2.1,var.com.2=est.sigma2.2$sigma2.2,
                                                                       ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                                       X.U=as.matrix(x.matrix.U),t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("conditional"))
# ------------------------------------------------------------------------------
# 3L model: Homoskedasticity
# ------------------------------------------------------------------------------
set.seed(2015)
NPELL.HM.3L.FGT.Estimate.UNC.UPOVLN<-ELL.NPB.HM.3L.FGT.Estimator.Scale(beta=beta.gls.3,var.beta=var.beta.gls.3,jeta.s=eta,eta.s=u,eps.s=sample.data.fitted$eps.3,var.com.1=est.sigma2.3$sigma2.1,var.com.2=est.sigma2.3$sigma2.2,var.com.3=est.sigma2.3$sigma2.3,
                                                                       ID.C.s=sample.data.fitted$PSU.ID,ID.D.s=sample.data.fitted$AREA.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                                       X.U=as.matrix(x.matrix.U),t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("unconditional"))
set.seed(2015)
NPELL.HM.3L.FGT.Estimate.CON.UPOVLN<-ELL.NPB.HM.3L.FGT.Estimator.Scale(beta=beta.gls.3,var.beta=var.beta.gls.3,jeta.s=eta,eta.s=u,eps.s=sample.data.fitted$eps.3,var.com.1=est.sigma2.3$sigma2.1,var.com.2=est.sigma2.3$sigma2.2,var.com.3=est.sigma2.3$sigma2.3,
                                                                       ID.C.s=sample.data.fitted$PSU.ID,ID.D.s=sample.data.fitted$AREA.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                                       X.U=as.matrix(x.matrix.U),t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("conditional"))
# ------------------------------------------------------------------------------
# Implementation of Non-parametric CDMC Methodology: Homoskedasticity
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted<-Census.data.fitted[order(Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]
# ------------------------------------------------------------------------------
# 2L model: Homoskedasticity
# ------------------------------------------------------------------------------
set.seed(2015)
BCDMC.HM.2L.FGT.Estimate.UNC.UPOVLN<-CD.MC.HM.2L.FGT.Estimator(beta=beta.gls.2,var.beta=var.beta.gls.2,eta.s=u.gls.2,eps.s=sample.data.fitted$eps.gls.2,
                                                               var.com.2=est.sigma2.2$sigma2.2,var.com.1=est.sigma2.2$sigma2.1,ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                               X.U=as.matrix(x.matrix.U),t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("unconditional"))
set.seed(2015)
BCDMC.HM.2L.FGT.Estimate.CON.UPOVLN<-CD.MC.HM.2L.FGT.Estimator(beta=beta.gls.2,var.beta=var.beta.gls.2,eta.s=u.gls.2,eps.s=sample.data.fitted$eps.gls.2,
                                                               var.com.2=est.sigma2.2$sigma2.2,var.com.1=est.sigma2.2$sigma2.1,ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                               X.U=as.matrix(x.matrix.U),t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("conditional"))
# ------------------------------------------------------------------------------
# 3L model: Homoskedasticity
# ------------------------------------------------------------------------------
set.seed(2015)
BCDMC.HM.3L.FGT.Estimate.UNC.UPOVLN<-CD.MC.HM.3L.FGT.Estimator(beta=beta.gls.3,var.beta=var.beta.gls.3,jeta.s=eta.gls.3,eta.s=u.gls.3,eps.s=sample.data.fitted$eps.gls.3,
                                                               var.com.3=est.sigma2.3$sigma2.3,var.com.2=est.sigma2.3$sigma2.2,var.com.1=est.sigma2.3$sigma2.1,
                                                               ID.C.s=sample.data.fitted$PSU.ID,ID.D.s=sample.data.fitted$AREA.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                               X.U=as.matrix(x.matrix.U),t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("unconditional"))
set.seed(2015)
BCDMC.HM.3L.FGT.Estimate.CON.UPOVLN<-CD.MC.HM.3L.FGT.Estimator(beta=beta.gls.3,var.beta=var.beta.gls.3,jeta.s=eta,eta.s=u,eps.s=sample.data.fitted$eps.3,
                                                               var.com.3=est.sigma2.3$sigma2.3,var.com.2=est.sigma2.3$sigma2.2,var.com.1=est.sigma2.3$sigma2.1,
                                                               ID.C.s=sample.data.fitted$PSU.ID,ID.D.s=sample.data.fitted$AREA.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                               X.U=as.matrix(x.matrix.U),t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("conditional"))
# ------------------------------------------------------------------------------
# Implementation of Non-parametric CDSM Methodology: Homoskedasticity
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted<-Census.data.fitted[order(Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]
# ------------------------------------------------------------------------------
# 2L model: Homoskedasticity
# ------------------------------------------------------------------------------
set.seed(2015)
BCDSM.HM.2L.FGT.Estimate.Fixed.UPOVLN<-CD.SM.HM.2L.FGT.Estimator(beta=beta.gls.2,var.beta=var.beta.gls.2,eta.s=as.vector(u.gls.2),
                                                                 eps.s=as.vector(sample.data.fitted$eps.gls.2),var.com.2=est.sigma2.2$sigma2.2,var.com.1=est.sigma2.2$sigma2.1,
                                                                 ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,ID.HH=Census.data.fitted$HH.ID,X.U=as.matrix(x.matrix.U),
                                                                 t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1="Fixed")
# ------------------------------------------------------------------------------
# 3L model: Homoskedasticity
# ------------------------------------------------------------------------------
set.seed(2015)
BCDSM.HM.3L.FGT.Estimate.Fixed.UPOVLN<-CD.SM.HM.3L.FGT.Estimator(beta=beta.gls.3,var.beta=var.beta.gls.3,jeta.s=eta.gls.3,eta.s=u.gls.3,eps.s=sample.data.fitted$eps.gls.3,
                                                                 var.com.3=est.sigma2.3$sigma2.3,var.com.2=est.sigma2.3$sigma2.2,var.com.1=est.sigma2.3$sigma2.1,
                                                                 ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,ID.HH=Census.data.fitted$HH.ID,
                                                                 X.U=as.matrix(x.matrix.U),t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("Fixed"))
# ------------------------------------------------------------------------------
# Two-level model using GLS method assuming HT Level-one errors 
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted<-Census.data.fitted[order(Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]
x.matrix.s.HT<-data.frame(hhhprmed=sample.data.fitted$hhhprmed,ibuild_4=sample.data.fitted$ibuild_4,idiv_1=sample.data.fitted$idiv_1,idiv_7=sample.data.fitted$idiv_7,
                          idiv_4=sample.data.fitted$idiv_4,idiv_5=sample.data.fitted$idiv_5,ilattr_1=sample.data.fitted$ilattr_1,literatep=sample.data.fitted$literatep,
                          ownaglnd=sample.data.fitted$ownaglnd,workst2p=sample.data.fitted$workst2p)
x.matrix.U.HT<-data.frame(hhhprmed=Census.data.fitted$hhhprmed,ibuild_4=Census.data.fitted$ibuild_4,idiv_1=Census.data.fitted$idiv_1,idiv_7=Census.data.fitted$idiv_7,
                          idiv_4=Census.data.fitted$idiv_4,idiv_5=Census.data.fitted$idiv_5,ilattr_1=Census.data.fitted$ilattr_1,literatep=Census.data.fitted$literatep,
                          ownaglnd=Census.data.fitted$ownaglnd,workst2p=Census.data.fitted$workst2p)
Ols.Full.2L<-lm(ln_p_expnd~electric+ilattr_1+ilattr_3+iwater1+ibuild_3*rural+owner*ibuild_4+workst2p+workst3p*rural+iincom_3+num_hh*rural+
                  num_hh2*rural+hhhprmed*rural+literatep+child5p+mhhsize+depratio+paginc+idiv_1+idiv_7+idiv_4+idiv_5+femalep.rural,data=sample.data.fitted)
sample.data.fitted$u.ch.2<-resid(Ols.Full.2L)
u.2L<-tapply.order(sample.data.fitted$u.ch.2,sample.data.fitted$PSU.ID,mean,unique(sample.data.fitted$PSU.ID))
sample.data.fitted$u.2L <- with(sample.data.fitted, ave(u.ch.2, PSU.ID, FUN=mean))
sample.data.fitted$eps.2L<-sample.data.fitted$u.ch.2-sample.data.fitted$u.2L # No application latter
sample.data.fitted$y.hat.2L<-fitted.values(Ols.Full.2L)
est.sigma2.2.HT<-Var.Com.MM.2.H(sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID,u.2L,sample.data.fitted$eps.2L)
est.sigma2.2.HT$sigma2.1<-summary(Ols.Full.2L)$sigma^2-est.sigma2.2.HT$sigma2.2
est.sigma2.2.HT$sigma2.2/(est.sigma2.2.HT$sigma2.1+est.sigma2.2.HT$sigma2.2)*100
# ------------------------------------------------------------------------------
# Estimation of Heteroskedasticity: Alpha Model in ELL Method - Two-level model 
# ------------------------------------------------------------------------------
Sigma2.ch.ELL<-sigma2.ch.ELL(sample.data.fitted$eps.2L,as.matrix(x.matrix.s.HT),as.matrix(x.matrix.U.HT))
alpha.hat<-Sigma2.ch.ELL$alpha
cov.alpha.hat<-Sigma2.ch.ELL$vcov.alpha
A<-Sigma2.ch.ELL$A
sigma2.alpha<-Sigma2.ch.ELL$sigma2.alpha
SE.alpha.model<-sqrt(diag(cov.alpha.hat))
t.value.alpha<-alpha.hat/SE.alpha.model
p.value.alpha<-2*(1-pt(abs(t.value.alpha),length(sample.data.fitted$eps.2)-length(alpha.hat)))
R2.alpha.model<-Sigma2.ch.ELL$R.squared
coef.table.alpha.ELL.HT<-round(data.frame(alpha=alpha.hat,SE=SE.alpha.model,t=t.value.alpha,prob=p.value.alpha),5)
sample.data.fitted$sig2.ch.hat.2L.ELL<-Sigma2.ch.ELL$sigma2.ch.s
Census.data.fitted$sig2.ch.hat.2L.ELL<-Sigma2.ch.ELL$sigma2.ch.U
X.ols<-model.matrix(Ols.Full.2L)
gls.lm2.HT.ELL<-GLS.EST.2L(sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID,est.sigma2.2.HT$sigma2.2,sample.data.fitted$sig2.ch.hat.2L.ELL,x.matrix=X.ols,sample.data.fitted$ln_p_expnd)
beta.gls.2.HT.ELL<-gls.lm2.HT.ELL$beta.gls
var.beta.gls.2.HT.ELL<-gls.lm2.HT.ELL$vcov.beta.gls
t.beta.gls.2<-beta.gls.2.HT.ELL/sqrt(diag(var.beta.gls.2.HT.ELL))
p.beta.gls.2<-2*(1-pt(abs(t.beta.gls.2),length(sample.data.fitted$ln_p_expnd)-length(beta.gls.2.HT.ELL)))
coef.table.beta.gls.2.HT<-round(data.frame(beta.gls.2=beta.gls.2.HT.ELL,SE=sqrt(diag(var.beta.gls.2.HT.ELL)),t=t.beta.gls.2,prob=p.beta.gls.2),5)
# ------------------------------------------------------------------------------
# Estimation of Heteroskedasticity: Stratification MOM Method - Two-level model 
# ------------------------------------------------------------------------------
quantiles<-seq(0,100,10)
results.IGLS<-RES.VAR.STRATA.IGLS.2L(sample.data.fitted$ln_p_expnd,as.matrix(x.matrix.s),sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID,as.matrix(x.matrix.U),
                                  Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID,quantiles,Iteration.no=100,tol=1e-50)
sample.data.fitted$sig2.ch.hat.2L.MOM<-results.IGLS$sig2.ch.hat.s
Census.data.fitted$sig2.ch.hat.2L.MOM<-results.IGLS$sig2.ch.hat.U
X.ols<-model.matrix(Ols.Full.2L)
gls.lm2.HT.STR<-GLS.EST.2L(sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID,est.sigma2.2.HT$sigma2.2,sample.data.fitted$sig2.ch.hat.2L.MOM,x.matrix=X.ols,sample.data.fitted$ln_p_expnd)
beta.gls.2.HT.STR<-gls.lm2.HT.STR$beta.gls
var.beta.gls.2.HT.STR<-gls.lm2.HT.STR$vcov.beta.gls
sample.data.fitted$u.ch.gls.2.STR<-sample.data.fitted$ln_p_expnd-X.ols%*%beta.gls.2.HT.STR
u.gls.2.STR<-tapply.order(sample.data.fitted$u.ch.gls.2.STR,sample.data.fitted$PSU.ID,mean,unique(sample.data.fitted$PSU.ID))
sample.data.fitted$u.gls.2.STR<-with(sample.data.fitted, ave(u.ch.gls.2.STR, PSU.ID, FUN=mean))
sample.data.fitted$eps.gls.2.STR<-sample.data.fitted$u.ch.gls.2.STR-sample.data.fitted$u.gls.2.STR
t.beta.gls.2.STR<-beta.gls.2.HT.STR/sqrt(diag(var.beta.gls.2.HT.STR))
p.beta.gls.2.STR<-2*(1-pt(abs(t.beta.gls.2.STR),n-length(var.beta.gls.2.HT.STR)))
coef.table.beta.gls.2.HT.STR<-round(data.frame(beta.gls.2=beta.gls.2.HT.STR,SE=sqrt(diag(var.beta.gls.2.HT.STR)),t=t.beta.gls.2.STR,prob=p.beta.gls.2.STR),5)
# ------------------------------------------------------------------------------
# Three-level model using GLS method assuming HT Level-one errors
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted<-Census.data.fitted[order(Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]
Ols.Full.3L<-lm(ln_p_expnd~electric+ilattr_1+ilattr_3+iwater1+ibuild_3*rural+owner*ibuild_4+workst2p+workst3p*rural+iincom_3+num_hh*rural+
                  num_hh2*rural+hhhprmed*rural+literatep+child5p+mhhsize+depratio+paginc+idiv_1+idiv_7+idiv_4+idiv_5+femalep.rural,data=sample.data.fitted)
sample.data.fitted$u.ch.3L<-resid(Ols.Full.3L)
u.3L<-tapply.order(sample.data.fitted$u.ch.3L,sample.data.fitted$PSU.ID,mean,unique(sample.data.fitted$PSU.ID))
eta.3L<-tapply.order(sample.data.fitted$u.ch.3L,sample.data.fitted$AREA.ID,mean,unique(sample.data.fitted$AREA.ID))
sample.data.fitted$u.3L <- with(sample.data.fitted, ave(u.ch.3L, PSU.ID, FUN=mean))
sample.data.fitted$eta.3L<-with(sample.data.fitted, ave(u.ch.3L, AREA.ID, FUN=mean))
sample.data.fitted$eps.3L<-sample.data.fitted$u.ch.3L-sample.data.fitted$u.3L-sample.data.fitted$eta.3L # No application latter
sample.data.fitted$y.hat.3L<-fitted.values(Ols.Full.3L)
est.sigma2.3.HT<-Var.Com.MM.3.H(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID,eta.3L,u.3L,sample.data.fitted$eps.3L)
est.sigma2.3.HT$sigma2.1<-summary(Ols.Full.3L)$sigma^2-est.sigma2.3.HT$sigma2.2-est.sigma2.3.HT$sigma2.3
est.sigma2.3.HT$sigma2.2/(est.sigma2.3.HT$sigma2.1+est.sigma2.3.HT$sigma2.2+est.sigma2.3.HT$sigma2.3)*100
est.sigma2.3.HT$sigma2.3/(est.sigma2.3.HT$sigma2.1+est.sigma2.3.HT$sigma2.2+est.sigma2.3.HT$sigma2.3)*100
# ------------------------------------------------------------------------------
# Estimation of Heteroskedasticity: Alpha Model in ELL Method - Three-level model 
# ------------------------------------------------------------------------------
Sigma2.ch.ELL.3L<-sigma2.ch.ELL(sample.data.fitted$eps.3L,as.matrix(x.matrix.s.HT),as.matrix(x.matrix.U.HT))

alpha.hat.3<-Sigma2.ch.ELL.3L$alpha
cov.alpha.hat.3<-Sigma2.ch.ELL.3L$vcov.alpha
A.3<-Sigma2.ch.ELL.3L$A
sigma2.alpha.3<-Sigma2.ch.ELL.3L$sigma2.alpha
SE.alpha.model.3<-sqrt(diag(cov.alpha.hat.3))
t.value.alpha.3<-alpha.hat.3/SE.alpha.model.3
p.value.alpha.3<-2*(1-pt(abs(t.value.alpha.3),length(sample.data.fitted$eps.3L)-length(alpha.hat.3)))
R2.alpha.model<-Sigma2.ch.ELL.3L$R.squared
coef.table.alpha.ELL.HT<-round(data.frame(alpha=alpha.hat.3,SE=SE.alpha.model.3,t=t.value.alpha.3,prob=p.value.alpha.3),5)
#write.csv(coef.table.alpha.ELL.HT,"C:/BD Poverty Mapping/coef.table.alpha.ELL.HT.csv")

sample.data.fitted$sig2.ch.hat.3L.ELL<-Sigma2.ch.ELL.3L$sigma2.ch.s
Census.data.fitted$sig2.ch.hat.3L.ELL<-Sigma2.ch.ELL.3L$sigma2.ch.U

X.ols<-model.matrix(Ols.Full.3L)
gls.lm2.HT.ELL.3L<-GLS.EST.3L(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID,
                              est.sigma2.3.HT$sigma2.3,est.sigma2.3.HT$sigma2.2,sample.data.fitted$sig2.ch.hat.3L.ELL,x.matrix=X.ols,sample.data.fitted$ln_p_expnd)

beta.gls.2.HT.ELL.3L<-gls.lm2.HT.ELL.3L$beta.gls
var.beta.gls.2.HT.ELL.3L<-gls.lm2.HT.ELL.3L$vcov.beta.gls
t.beta.gls.2.3L<-beta.gls.2.HT.ELL.3L/sqrt(diag(var.beta.gls.2.HT.ELL.3L))
p.beta.gls.2.3L<-2*(1-pt(abs(t.beta.gls.2.3L),length(sample.data.fitted$ln_p_expnd)-length(beta.gls.2.HT.ELL.3L)))
coef.table.beta.gls.2.HT.3L<-round(data.frame(beta.gls.2=beta.gls.2.HT.ELL.3L,SE=sqrt(diag(var.beta.gls.2.HT.ELL.3L)),t=t.beta.gls.2.3L,prob=p.beta.gls.2.3L),5)
# ------------------------------------------------------------------------------
# Estimation of Heteroskedasticity: Stratification MOM Method - Three-level model 
# ------------------------------------------------------------------------------
quantiles<-seq(0,100,10)
results.IGLS.3L<-RES.VAR.STRATA.IGLS.3L(sample.data.fitted$ln_p_expnd,as.matrix(x.matrix.s),sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID,
                                        as.matrix(x.matrix.U),Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID,quantiles,Iteration.no=20,tol=1e-10)
sample.data.fitted$sig2.ch.hat.3L.MOM<-results.IGLS.3L$sig2.ch.hat.s
Census.data.fitted$sig2.ch.hat.3L.MOM<-results.IGLS.3L$sig2.ch.hat.U
gls.lm3.HT.STR<-GLS.EST.3L(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID,
                           results.IGLS.3L$sigma2.3,results.IGLS.3L$sigma2.2,sample.data.fitted$sig2.ch.hat.3L.MOM,
                           x.matrix=X.ols,sample.data.fitted$ln_p_expnd)
beta.gls.3.HT.STR<-gls.lm3.HT.STR$beta.gls
var.beta.gls.3.HT.STR<-gls.lm3.HT.STR$vcov.beta.gls
sample.data.fitted$u.ch.gls.3.STR<-sample.data.fitted$ln_p_expnd-X.ols%*%beta.gls.3.HT.STR
u.gls.3.STR<-tapply.order(sample.data.fitted$u.ch.gls.3.STR,sample.data.fitted$PSU.ID,mean,unique(sample.data.fitted$PSU.ID))
eta.gls.3.STR<-tapply.order(sample.data.fitted$u.ch.gls.3.STR,sample.data.fitted$AREA.ID,mean,unique(sample.data.fitted$AREA.ID))
sample.data.fitted$u.gls.3.STR<-with(sample.data.fitted, ave(u.ch.gls.3.STR, PSU.ID, FUN=mean))
sample.data.fitted$eta.gls.3.STR<-with(sample.data.fitted, ave(u.ch.gls.3.STR, AREA.ID, FUN=mean))
sample.data.fitted$eps.gls.3.STR<-sample.data.fitted$u.ch.gls.3.STR-sample.data.fitted$u.gls.3.STR-sample.data.fitted$eta.gls.3.STR
t.beta.gls.3.STR<-beta.gls.3.HT.STR/sqrt(diag(var.beta.gls.3.HT.STR))
p.beta.gls.3.STR<-2*(1-pt(abs(t.beta.gls.3.STR),length(sample.data.fitted$ln_p_expnd)-length(beta.gls.3.HT.STR)))
coef.table.beta.gls.3.HT.STR<-round(data.frame(beta.gls.3=beta.gls.3.HT.STR,SE=sqrt(diag(var.beta.gls.3.HT.STR)),t=t.beta.gls.3.STR,prob=p.beta.gls.3.STR),5)
# ------------------------------------------------------------------------------
# Implementation of Parametric ELL Methodology: Heteroskedasticity
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted<-Census.data.fitted[order(Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]
# ------------------------------------------------------------------------------#
# 2L model: Heteroskedasticity
# ------------------------------------------------------------------------------#
set.seed(2015)
ELL.PB.2L.HT.FGT.Estimate.PP.UPOVLN<-ELL.PB.HT.2L.FGT.Estimator(beta=beta.gls.2.HT.ELL,var.beta=var.beta.gls.2.HT.ELL,alpha=alpha.hat,var.alpha=cov.alpha.hat,
                                                                sigma2.alpha=sigma2.alpha,var.com.2=est.sigma2.2.HT$sigma2.2,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,X.U.HT=as.matrix(x.matrix.U.HT),
                                                                X.U=as.matrix(x.matrix.U),A=A,t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5)
# ------------------------------------------------------------------------------#
# 3L model: Heteroskedasticity
# ------------------------------------------------------------------------------#
set.seed(2015)
ELL.PB.3L.HT.FGT.Estimate.PP.UPOVLN<-ELL.PB.HT.3L.FGT.Estimator(beta=beta.gls.2.HT.ELL.3L,var.beta=var.beta.gls.2.HT.ELL.3L,alpha=alpha.hat,var.alpha=cov.alpha.hat,sigma2.alpha=sigma2.alpha,
                                                                var.com.2=est.sigma2.3.HT$sigma2.2,var.com.3=est.sigma2.3.HT$sigma2.3,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                                X.U.HT=as.matrix(x.matrix.U.HT),X.U=as.matrix(x.matrix.U),A=A.3,Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5)
# ------------------------------------------------------------------------------
# Implementation of Semi-Parametric ELL Methodology: Heteroskedasticity
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted<-Census.data.fitted[order(Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]
# ------------------------------------------------------------------------------#
# 2L model: Heteroskedasticity
# ------------------------------------------------------------------------------#
set.seed(2015)
SPELL.HT.2L.FGT.Estimate.Scale.UNC.UPOVLN<-ELL.NPB.HT.2L.FGT.Estimator.Scale(beta=beta.gls.2.HT.ELL,var.beta=var.beta.gls.2.HT.ELL,alpha=alpha.hat,var.alpha=cov.alpha.hat,
                                                                             sigma2.alpha=sigma2.alpha,eta.s=u.2L,eps.s=sample.data.fitted$eps.2L,
                                                                             var.com.2=est.sigma2.2.HT$sigma2.2,var.com.1=mean(sample.data.fitted$sig2.ch.hat.2L.ELL),sig2.eps.s=sample.data.fitted$sig2.ch.hat.2L.ELL,
                                                                             ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                                             X.U.HT=as.matrix(x.matrix.U.HT),X.U=as.matrix(x.matrix.U),A=A,t=Census.data.fitted$upovln,
                                                                             HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("unconditional"))
set.seed(2015)
SPELL.HT.2L.FGT.Estimate.Scale.CON.UPOVLN<-ELL.NPB.HT.2L.FGT.Estimator.Scale(beta=beta.gls.2.HT.ELL,var.beta=var.beta.gls.2.HT.ELL,alpha=alpha.hat,var.alpha=cov.alpha.hat,
                                                                             sigma2.alpha=sigma2.alpha,eta.s=u.2L,eps.s=sample.data.fitted$eps.2L,
                                                                             var.com.2=est.sigma2.2.HT$sigma2.2,var.com.1=mean(sample.data.fitted$sig2.ch.hat.2L.ELL),sig2.eps.s=sample.data.fitted$sig2.ch.hat.2L.ELL,
                                                                             ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                                             X.U.HT=as.matrix(x.matrix.U.HT),X.U=as.matrix(x.matrix.U),A=A,t=Census.data.fitted$upovln,
                                                                             HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("conditional"))
# ------------------------------------------------------------------------------#
# 3L model: Heteroskedasticity
# ------------------------------------------------------------------------------#
set.seed(2015)
SPELL.HT.3L.FGT.Estimate.Scale.UNC.UPOVLN<-ELL.NPB.HT.3L.FGT.Estimator.Scale(beta=beta.gls.2.HT.ELL.3L,var.beta=var.beta.gls.2.HT.ELL.3L,alpha=alpha.hat,var.alpha=cov.alpha.hat,sigma2.alpha=sigma2.alpha,
                                                                             jeta.s=eta.3L,eta.s=u.3L,eps.s=sample.data.fitted$eps.3L,var.com.3=est.sigma2.3.HT$sigma2.3,var.com.2=est.sigma2.3.HT$sigma2.2,var.com.1=mean(sample.data.fitted$sig2.ch.hat.3L.ELL),sig2.eps.s=sample.data.fitted$sig2.ch.hat.3L.ELL,
                                                                             ID.C.s=sample.data.fitted$PSU.ID,ID.D.s=sample.data.fitted$AREA.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,X.U.HT=as.matrix(x.matrix.U.HT),
                                                                             X.U=as.matrix(x.matrix.U),A.3,Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("unconditional"))
set.seed(2015)
SPELL.HT.3L.FGT.Estimate.Scale.CON.UPOVLN<-ELL.NPB.HT.3L.FGT.Estimator.Scale(beta=beta.gls.2.HT.ELL.3L,var.beta=var.beta.gls.2.HT.ELL.3L,alpha=alpha.hat,var.alpha=cov.alpha.hat,sigma2.alpha=sigma2.alpha,
                                                                             jeta.s=eta.3L,eta.s=u.3L,eps.s=sample.data.fitted$eps.3L,var.com.3=est.sigma2.3.HT$sigma2.3,var.com.2=est.sigma2.3.HT$sigma2.2,var.com.1=mean(sample.data.fitted$sig2.ch.hat.3L.ELL),sig2.eps.s=sample.data.fitted$sig2.ch.hat.3L.ELL,
                                                                             ID.C.s=sample.data.fitted$PSU.ID,ID.D.s=sample.data.fitted$AREA.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,X.U.HT=as.matrix(x.matrix.U.HT),
                                                                             X.U=as.matrix(x.matrix.U),A.3,Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("conditional"))
# ------------------------------------------------------------------------------
# Implementation of CDMC Methodology: Heteroskedasticity
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted<-Census.data.fitted[order(Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]
# ------------------------------------------------------------------------------#
# 2L model: Heteroskedasticity
# ------------------------------------------------------------------------------#
set.seed(2015)
BCDMC.HT.2L.FGT.Estimate.UNC.Scale.UPOVLN<-CD.MC.HT.2L.FGT.Estimator.Scale(beta=beta.gls.2.HT.STR,var.beta=var.beta.gls.2.HT.STR,eta.s=u.gls.2.STR,eps.s=sample.data.fitted$eps.gls.2.STR,
                                                                           var.com.2=est.sigma2.2.HT$sigma2.2,var.com.1=est.sigma2.2.HT$sigma2.1,var.com.HH.s=sample.data.fitted$sig2.ch.hat.2L.MOM,var.com.HH.U=Census.data.fitted$sig2.ch.hat.2L.MOM,
                                                                           ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                                           X.U=as.matrix(x.matrix.U),t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("unconditional"))
set.seed(2015)
BCDMC.HT.2L.FGT.Estimate.CON.Scale.UPOVLN<-CD.MC.HT.2L.FGT.Estimator.Scale(beta=beta.gls.2.HT.STR,var.beta=var.beta.gls.2.HT.STR,eta.s=u.gls.2.STR,eps.s=sample.data.fitted$eps.gls.2.STR,
                                                                           var.com.2=est.sigma2.2.HT$sigma2.2,var.com.1=est.sigma2.2.HT$sigma2.1,var.com.HH.s=sample.data.fitted$sig2.ch.hat.2L.MOM,var.com.HH.U=Census.data.fitted$sig2.ch.hat.2L.MOM,
                                                                           ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                                           X.U=as.matrix(x.matrix.U),t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("conditional"))
# ------------------------------------------------------------------------------#
# 3L model: Heteroskedasticity
# ------------------------------------------------------------------------------#
set.seed(2015)
BCDMC.HT.3L.FGT.Estimate.UNC.Scale.UPOVLN<-CD.MC.HT.3L.FGT.Estimator.Scale(beta=beta.gls.3.HT.STR,var.beta=var.beta.gls.3.HT.STR,jeta.s=eta.gls.3.STR,eta.s=u.gls.3.STR,eps.s=sample.data.fitted$eps.gls.3.STR,
                                                                           var.com.3=est.sigma2.3.HT$sigma2.3,var.com.2=est.sigma2.3.HT$sigma2.2,var.com.1=est.sigma2.3.HT$sigma2.1,var.com.HH.s=sample.data.fitted$sig2.ch.hat.3L.MOM,var.com.HH.U=Census.data.fitted$sig2.ch.hat.3L.MOM,
                                                                           ID.C.s=sample.data.fitted$PSU.ID,ID.D.s=sample.data.fitted$AREA.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                                           X.U=as.matrix(x.matrix.U),t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("unconditional"))
set.seed(2015)
BCDMC.HT.3L.FGT.Estimate.CON.Scale.UPOVLN<-CD.MC.HT.3L.FGT.Estimator.Scale(beta=beta.gls.3.HT.STR,var.beta=var.beta.gls.3.HT.STR,jeta.s=eta.gls.3.STR,eta.s=u.gls.3.STR,eps.s=sample.data.fitted$eps.gls.3.STR,
                                                                           var.com.3=est.sigma2.3.HT$sigma2.3,var.com.2=est.sigma2.3.HT$sigma2.2,var.com.1=est.sigma2.3.HT$sigma2.1,var.com.HH.s=sample.data.fitted$sig2.ch.hat.3L.MOM,var.com.HH.U=Census.data.fitted$sig2.ch.hat.3L.MOM,
                                                                           ID.C.s=sample.data.fitted$PSU.ID,ID.D.s=sample.data.fitted$AREA.ID,ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,
                                                                           X.U=as.matrix(x.matrix.U),t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1=c("conditional"))
# ------------------------------------------------------------------------------
# Implementation of CDSM Methodology: Heteroskedasticity
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted<-Census.data.fitted[order(Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]
# ------------------------------------------------------------------------------#
# 2L model: Heteroskedasticity
# ------------------------------------------------------------------------------#
set.seed(2015)
BCDSM.HT.2L.FGT.Estimate.Fixed.UPOVLN.Scale<-CD.SM.HT.2L.FGT.Estimator.Scale(beta=beta.gls.2.HT.STR,var.beta=var.beta.gls.2.HT.STR,eta.s=as.vector(u.gls.2.STR),
                                                                             eps.s=as.vector(sample.data.fitted$eps.gls.2.STR),var.com.2=est.sigma2.2.HT$sigma2.2,var.com.1=est.sigma2.2.HT$sigma2.1,
                                                                             var.com.HH.s=as.vector(sample.data.fitted$sig2.ch.hat.2L.MOM),var.com.HH.U=as.vector(Census.data.fitted$sig2.ch.hat.2L.MOM),
                                                                             ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,ID.HH=Census.data.fitted$HH.ID,X.U=as.matrix(x.matrix.U),
                                                                             t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1="Fixed")

# ------------------------------------------------------------------------------#
# 3L model: Heteroskedasticity
# ------------------------------------------------------------------------------#
set.seed(2015)
BCDSM.HT.3L.FGT.Estimate.Fixed.UPOVLN.Scale<-CD.SM.HT.3L.FGT.Estimator.Scale(beta=beta.gls.3.HT.STR,var.beta=var.beta.gls.3.HT.STR,jeta.s=as.vector(eta.gls.3.STR),eta.s=as.vector(u.gls.3.STR),
                                                                             eps.s=as.vector(sample.data.fitted$eps.gls.3.STR),var.com.3=est.sigma2.3.HT$sigma2.3,var.com.2=est.sigma2.3.HT$sigma2.2,var.com.1=est.sigma2.3.HT$sigma2.1,
                                                                             var.com.HH.s=as.vector(sample.data.fitted$sig2.ch.hat.3L.MOM),var.com.HH.U=as.vector(Census.data.fitted$sig2.ch.hat.3L.MOM),
                                                                             ID.D=Census.data.fitted$AREA.ID,ID.C=Census.data.fitted$PSU.ID,ID.HH=Census.data.fitted$HH.ID,X.U=as.matrix(x.matrix.U),
                                                                             t=Census.data.fitted$upovln,HH.Size=Census.data.fitted$HH.size.U,No.Boot=5,residual.1="Fixed")
# ------------------------------------------------------------------------------
# Modified ELL Methodology: Construction of Strata based on number of HH and PPP
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted<-Census.data.fitted[order(Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]

ID.Area.s<-unique(sample.data.fitted$AREA.ID)
No.Area.s<-length(ID.Area.s)

ID.Area.U<-unique(Census.data.fitted$AREA.ID)
No.Area.U<-length(ID.Area.U)

Ki.s<-NULL    # Adjustment factor by area from sample structure: Unweighted 
Ki.P<-NULL    # Adjustment factor by area from population structure : Unweighted 

for (d in ID.Area.s){
  nij<-tapply(sample.data.fitted$HH.ID[sample.data.fitted$AREA.ID==d],sample.data.fitted$PSU.ID[sample.data.fitted$AREA.ID==d],length)
  Ki.s<-c(Ki.s,sum(nij)^2/sum(nij^2)) ## Adjustment factor by area
}

for (d in ID.Area.U){
  Nij<-tapply(Census.data.fitted$HH.ID[Census.data.fitted$AREA.ID==d],Census.data.fitted$PSU.ID[Census.data.fitted$AREA.ID==d],length)
  Ki.P<-c(Ki.P,sum(Nij)^2/sum(Nij^2)) ## Adjustment factor by area from population structure
}

No.HH.Area.U<-tapply.order(Census.data.fitted$HH.ID,Census.data.fitted$AREA.ID,length,unique(Census.data.fitted$AREA.ID))
No.HH.Area.s<-tapply.order(sample.data.fitted$HH.ID,sample.data.fitted$AREA.ID,length,unique(sample.data.fitted$AREA.ID))

HH.Ki.s<-NULL    ## Adjustment factor by area from sample structure : HH Weighted 
HH.Ki.P<-NULL    ## Adjustment factor by area from population structure : HH Weighted 

for (d in ID.Area.s){
  hij<-tapply(sample.data.fitted$HH.size.U[sample.data.fitted$AREA.ID==d],sample.data.fitted$PSU.ID[sample.data.fitted$AREA.ID==d],sum)
  HH.Ki.s<-c(HH.Ki.s,sum(hij)^2/sum(hij^2)) ## Adjustment factor by area
}

for (d in ID.Area.U){
  hij<-tapply(Census.data.fitted$HH.size.U[Census.data.fitted$AREA.ID==d],Census.data.fitted$PSU.ID[Census.data.fitted$AREA.ID==d],sum)
  HH.Ki.P<-c(HH.Ki.P,sum(hij)^2/sum(hij^2)) ## Adjustment factor by area
}

No.PP.Area.U<-tapply.order(Census.data.fitted$HH.size.U,Census.data.fitted$AREA.ID,sum,unique(Census.data.fitted$AREA.ID))
No.PP.Area.s<-tapply.order(sample.data.fitted$HH.size.U,sample.data.fitted$AREA.ID,sum,unique(sample.data.fitted$AREA.ID))

# ------------------------------------------------------------------------------#
# Stratum creation for 3rd adjustment factor
group<-c(0,0.20,0.35,0.50,0.65,0.80,1)
Stratum.by.Size<-data.frame(ID.Area.U=ID.Area.U,No.HH.Area.U=No.HH.Area.U,No.PP.Area.U=No.PP.Area.U,Ki.P=Ki.P,HH.Ki.P=HH.Ki.P)
Stratum.by.Size<-within(Stratum.by.Size, decile <- as.integer(cut(No.HH.Area.U, quantile(No.HH.Area.U, probs=group), include.lowest=TRUE, labels=FALSE)))
Stratum.by.Size<-within(Stratum.by.Size, PP.decile <- as.integer(cut(No.PP.Area.U, quantile(No.PP.Area.U, probs=group), include.lowest=TRUE, labels=FALSE)))
table(Stratum.by.Size$decile)
table(Stratum.by.Size$PP.decile)

Census.data.fitted<-Census.data.fitted[order(Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]
Census.data.fitted$Stratum.by.Size<-0
for (d in unique(Stratum.by.Size$decile)){
  Census.data.fitted$Stratum.by.Size[Census.data.fitted$AREA.ID%in%Stratum.by.Size$ID.Area.U[which(Stratum.by.Size$decile==unique(Stratum.by.Size$decile)[d])]]<-unique(Stratum.by.Size$decile)[d]
}

tapply(Stratum.by.Size$No.HH.Area.U,Stratum.by.Size$decile,sum)
table(Census.data.fitted$Stratum.by.Size)

Census.data.fitted$Stratum.by.PP.Size<-0
for (d in unique(Stratum.by.Size$decile)){
  Census.data.fitted$Stratum.by.PP.Size[Census.data.fitted$AREA.ID%in%Stratum.by.Size$ID.Area.U[which(Stratum.by.Size$PP.decile==unique(Stratum.by.Size$PP.decile)[d])]]<-unique(Stratum.by.Size$PP.decile)[d]
}

tapply(Stratum.by.Size$No.PP.Area.U,Stratum.by.Size$PP.decile,sum)
tapply(Census.data.fitted$HH.size.U,Census.data.fitted$Stratum.by.PP.Size,sum)

# Blockwise parameter by number of HHs ------------------------------------------------------------------------#
ID.Block.U<-Census.data.fitted$Stratum.by.Size
Block.ID<-unique(Census.data.fitted$Stratum.by.Size)
NoBlock<-length(unique(Census.data.fitted$Stratum.by.Size))

Ki.Block<-list(); for(i in 1:NoBlock) Ki.Block[[i]]<-Ki.P[unique(as.numeric(as.factor(Census.data.fitted$AREA.ID))[ID.Block.U==i])]
Cluster.B<-list(); for(i in 1:NoBlock) Cluster.B[[i]]<-unique(as.numeric(as.factor(Census.data.fitted$PSU.ID))[ID.Block.U==i])
No.Cluster.B<-list(); for(i in 1:NoBlock) No.Cluster.B[[i]]<-length(Cluster.B[[i]])
N.B<-list(); for(i in 1:NoBlock) N.B[[i]]<-length(Census.data.fitted$PSU.ID[ID.Block.U==i])

# Blockwise parameter by number of population ------------------------------------------------------------------------#
ID.Block.U.PP<-Census.data.fitted$Stratum.by.PP.Size
Block.ID.PP<-unique(Census.data.fitted$Stratum.by.PP.Size)
NoBlock.PP<-length(unique(Census.data.fitted$Stratum.by.PP.Size))

Ki.Block.PP<-list(); for(i in 1:NoBlock.PP) Ki.Block.PP[[i]]<-HH.Ki.P[unique(as.numeric(as.factor(Census.data.fitted$AREA.ID))[ID.Block.U.PP==i])]
Cluster.B.PP<-list(); for(i in 1:NoBlock.PP) Cluster.B.PP[[i]]<-unique(as.numeric(as.factor(Census.data.fitted$PSU.ID))[ID.Block.U.PP==i])
No.Cluster.B.PP<-list(); for(i in 1:NoBlock.PP) No.Cluster.B.PP[[i]]<-length(Cluster.B.PP[[i]])
N.B.PP<-list(); for(i in 1:NoBlock.PP) N.B.PP[[i]]<-length(Census.data.fitted$PSU.ID[ID.Block.U.PP==i])
# ------------------------------------------------------------------------------
# Adjustment factors: Under Homoskedasticty 
# ------------------------------------------------------------------------------

# 1st adjustment factor
K1<-(est.sigma2.3$sigma2.2+mean(Ki.s)*est.sigma2.3$sigma2.3)/est.sigma2.3$sigma2.2
HH.K1<-(est.sigma2.3$sigma2.2+mean(HH.Ki.s)*est.sigma2.3$sigma2.3)/est.sigma2.2$sigma2.2
# ------------------------------------------------------------------------------#

# 2nd adjustment factor
K2<-(est.sigma2.3$sigma2.2+mean(Ki.P)*est.sigma2.3$sigma2.3)/est.sigma2.2$sigma2.2
HH.K2<-(est.sigma2.3$sigma2.2+mean(HH.Ki.P)*est.sigma2.3$sigma2.3)/est.sigma2.2$sigma2.2
# ------------------------------------------------------------------------------#

# 3rd adjustment factor: Block wise according to HH
K3<-list(); for(i in 1:NoBlock) K3[[i]]<-(est.sigma2.3$sigma2.2+mean(Ki.Block[[i]])*est.sigma2.3$sigma2.3)/est.sigma2.2$sigma2.2
adj.lemda2.2.K3.i<-list(); for(i in 1:NoBlock) adj.lemda2.2.K3.i[[i]]<-K3[[i]]*est.sigma2.2$sigma2.2
# 3rd adjustment factor: Block wise according to PP
K3.PP<-list(); for(i in 1:NoBlock.PP) K3.PP[[i]]<-(est.sigma2.3$sigma2.2+mean(Ki.Block.PP[[i]])*est.sigma2.3$sigma2.3)/est.sigma2.2$sigma2.2
adj.lemda2.2.K3.PP.i<-list(); for(i in 1:NoBlock.PP) adj.lemda2.2.K3.PP.i[[i]]<-K3.PP[[i]]*est.sigma2.2$sigma2.2
# ------------------------------------------------------------------------------
# Adjustment factors: Under Heteroskedasticity 
# ------------------------------------------------------------------------------

# 1st adjustment factor: PP
HH.K1.HT<-(est.sigma2.3.HT$sigma2.2+mean(HH.Ki.s)*est.sigma2.3.HT$sigma2.3)/est.sigma2.2.HT$sigma2.2

# 2nd adjustment factor: PP
HH.K2.HT<-(est.sigma2.3.HT$sigma2.2+mean(HH.Ki.P)*est.sigma2.3.HT$sigma2.3)/est.sigma2.2.HT$sigma2.2

# 3rd adjustment factor: Block wise according to PP
K3.PP.HT<-list(); for(i in 1:NoBlock.PP) K3.PP.HT[[i]]<-(est.sigma2.3.HT$sigma2.2+mean(Ki.Block.PP[[i]])*est.sigma2.3.HT$sigma2.3)/est.sigma2.2.HT$sigma2.2
adj.lemda2.2.K3.PP.i.HT<-list(); for(i in 1:NoBlock.PP) adj.lemda2.2.K3.PP.i.HT[[i]]<-K3.PP.HT[[i]]*est.sigma2.2.HT$sigma2.2
# ------------------------------------------------------------------------------
# Data sets for implementing Modified ELL (MELL) Methodology under Homoskedasticity & Heteroskedasticity
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted.Stratum<-Census.data.fitted[order(Census.data.fitted$Stratum.by.PP.Size, Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]

x.matrix.U.Stratum<-data.frame(Census.data.fitted.Stratum$electric,Census.data.fitted.Stratum$ilattr_1,Census.data.fitted.Stratum$ilattr_3,Census.data.fitted.Stratum$iwater1,Census.data.fitted.Stratum$ibuild_3,Census.data.fitted.Stratum$rural,
                               Census.data.fitted.Stratum$owner,Census.data.fitted.Stratum$ibuild_4,Census.data.fitted.Stratum$workst2p,Census.data.fitted.Stratum$workst3p,Census.data.fitted.Stratum$iincom_3,
                               Census.data.fitted.Stratum$num_hh,Census.data.fitted.Stratum$num_hh2,Census.data.fitted.Stratum$hhhprmed,Census.data.fitted.Stratum$literatep,Census.data.fitted.Stratum$child5p,
                               Census.data.fitted.Stratum$mhhsize,Census.data.fitted.Stratum$depratio,Census.data.fitted.Stratum$paginc,Census.data.fitted.Stratum$idiv_1,
                               Census.data.fitted.Stratum$idiv_7,Census.data.fitted.Stratum$idiv_4,Census.data.fitted.Stratum$idiv_5,Census.data.fitted.Stratum$femalep.rural,
                               Census.data.fitted.Stratum$ibuild_3*Census.data.fitted.Stratum$rural,Census.data.fitted.Stratum$owner*Census.data.fitted.Stratum$ibuild_4,
                               Census.data.fitted.Stratum$workst3p*Census.data.fitted.Stratum$rural,Census.data.fitted.Stratum$num_hh*Census.data.fitted.Stratum$rural,
                               Census.data.fitted.Stratum$num_hh2*Census.data.fitted.Stratum$rural,Census.data.fitted.Stratum$hhhprmed*Census.data.fitted.Stratum$rural)
dim(x.matrix.U.Stratum)

x.matrix.U.HT.Stratum<-data.frame(hhhprmed=Census.data.fitted.Stratum$hhhprmed,ibuild_4=Census.data.fitted.Stratum$ibuild_4,idiv_1=Census.data.fitted.Stratum$idiv_1,idiv_7=Census.data.fitted.Stratum$idiv_7,
                                  idiv_4=Census.data.fitted.Stratum$idiv_4,idiv_5=Census.data.fitted.Stratum$idiv_5,ilattr_1=Census.data.fitted.Stratum$ilattr_1,literatep=Census.data.fitted.Stratum$literatep,
                                  ownaglnd=Census.data.fitted.Stratum$ownaglnd,workst2p=Census.data.fitted.Stratum$workst2p)
# ------------------------------------------------------------------------------
# Implementation of Parametric MELL (MPELL) Methodology Under HM & HT 
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted.Stratum<-Census.data.fitted[order(Census.data.fitted$Stratum.by.PP.Size, Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]

set.seed(2015)
M3.PELL.HM.2L.FGT.Estimate.PP.UPOVLN<-MELL.PB.HM.2L.FGT.Estimator(beta=beta.gls.2,var.beta=var.beta.gls.2,var.com.1=est.sigma2.2$sigma2.1,
           Mod.var.com.2=c(unlist(adj.lemda2.2.K3.PP.i)), NoClusterBlock=c(unlist(No.Cluster.B.PP)),
           ID.D=Census.data.fitted.Stratum$AREA.ID,ID.C=Census.data.fitted.Stratum$PSU.ID,X.U=as.matrix(x.matrix.U.Stratum),t=Census.data.fitted.Stratum$upovln,
           HH.Size=Census.data.fitted.Stratum$HH.size.U,No.Boot=5)
set.seed(2015)
M3.PELL.HT.2L.FGT.Estimate.PP.UPOVLN<-MELL.PB.HT.2L.FGT.Estimator(beta=beta.gls.2.HT.ELL,var.beta=var.beta.gls.2.HT.ELL,alpha=alpha.hat,var.alpha=cov.alpha.hat,
           sigma2.alpha=sigma2.alpha,Mod.var.com.2=c(unlist(adj.lemda2.2.K3.PP.i.HT)),NoClusterBlock=c(unlist(No.Cluster.B.PP)),
           ID.D=Census.data.fitted.Stratum$AREA.ID,ID.C=Census.data.fitted.Stratum$PSU.ID,X.U.HT=as.matrix(x.matrix.U.HT.Stratum),X.U=as.matrix(x.matrix.U.Stratum),A=A,t=Census.data.fitted.Stratum$upovln,
           HH.Size=Census.data.fitted.Stratum$HH.size.U,No.Boot=5)
# ------------------------------------------------------------------------------
# Implementation of Semi/Non-Parametric MELL (MNPELL/MSPELL) Methodology Under HM & HT 
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted.Stratum<-Census.data.fitted[order(Census.data.fitted$Stratum.by.PP.Size, Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]

set.seed(2015)
M3.NPELL.HM.2L.FGT.Estimate.UNC.PP.UPOVLN<-MELL.NPB.HM.2L.FGT.Estimator(beta=beta.gls.2,var.beta=var.beta.gls.2,eta.s=u,eps.s=sample.data.fitted$eps.2,
           var.com.1=est.sigma2.2$sigma2.1,var.com.2=est.sigma2.2$sigma2.2,
           Mod.var.com.2=c(unlist(adj.lemda2.2.K3.PP.i)),NoClusterBlock=c(unlist(No.Cluster.B.PP)),
           ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted.Stratum$AREA.ID,ID.C=Census.data.fitted.Stratum$PSU.ID,
           X.U=as.matrix(x.matrix.U.Stratum),t=Census.data.fitted.Stratum$upovln,HH.Size=Census.data.fitted.Stratum$HH.size.U,No.Boot=5,residual.1=c("unconditional"))
set.seed(2015)
M3.NPELL.HM.2L.FGT.Estimate.CON.PP.UPOVLN<-MELL.NPB.HM.2L.FGT.Estimator(beta=beta.gls.2,var.beta=var.beta.gls.2,eta.s=u,eps.s=sample.data.fitted$eps.2,
          var.com.1=est.sigma2.2$sigma2.1,var.com.2=est.sigma2.2$sigma2.2,
          Mod.var.com.2=c(unlist(adj.lemda2.2.K3.PP.i)),NoClusterBlock=c(unlist(No.Cluster.B.PP)),
          ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted.Stratum$AREA.ID,ID.C=Census.data.fitted.Stratum$PSU.ID,
          X.U=as.matrix(x.matrix.U.Stratum),t=Census.data.fitted.Stratum$upovln,HH.Size=Census.data.fitted.Stratum$HH.size.U,No.Boot=5,residual.1=c("conditional"))

set.seed(2015)
M3.SPELL.HT.2L.FGT.Estimate.UNC.PP.Scale.UPOVLN<-MELL.NPB.HT.2L.FGT.Estimator.Scale(beta=beta.gls.2.HT.ELL,var.beta=var.beta.gls.2.HT.ELL,alpha=alpha.hat,var.alpha=cov.alpha.hat,sigma2.alpha=sigma2.alpha,
         eta.s=u.2L,var.com.2=est.sigma2.2.HT$sigma2.2,var.com.1=mean(sample.data.fitted$sig2.ch.hat.2L.ELL),Mod.var.com.2=c(unlist(adj.lemda2.2.K3.PP.i.HT)),NoClusterBlock=c(unlist(No.Cluster.B.PP)),
         eps.s=sample.data.fitted$eps.2L,sig2.eps.s=sample.data.fitted$sig2.ch.hat.2L.ELL,
         ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted.Stratum$AREA.ID,ID.C=Census.data.fitted.Stratum$PSU.ID,
         X.U.HT=as.matrix(x.matrix.U.HT.Stratum),X.U=as.matrix(x.matrix.U.Stratum),A=A,t=Census.data.fitted.Stratum$upovln,
         HH.Size=Census.data.fitted.Stratum$HH.size.U,No.Boot=5,residual.1="unconditional")
set.seed(2015)
M3.SPELL.HT.2L.FGT.Estimate.CON.PP.Scale.UPOVLN<-MELL.NPB.HT.2L.FGT.Estimator.Scale(beta=beta.gls.2.HT.ELL,var.beta=var.beta.gls.2.HT.ELL,alpha=alpha.hat,var.alpha=cov.alpha.hat,sigma2.alpha=sigma2.alpha,
         eta.s=u.2L,var.com.2=est.sigma2.2.HT$sigma2.2,var.com.1=mean(sample.data.fitted$sig2.ch.hat.2L.ELL),Mod.var.com.2=c(unlist(adj.lemda2.2.K3.PP.i.HT)),NoClusterBlock=c(unlist(No.Cluster.B.PP)),
         eps.s=sample.data.fitted$eps.2L,sig2.eps.s=sample.data.fitted$sig2.ch.hat.2L.ELL,
         ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted.Stratum$AREA.ID,ID.C=Census.data.fitted.Stratum$PSU.ID,
         X.U.HT=as.matrix(x.matrix.U.HT.Stratum),X.U=as.matrix(x.matrix.U.Stratum),A=A,t=Census.data.fitted.Stratum$upovln,
         HH.Size=Census.data.fitted.Stratum$HH.size.U,No.Boot=5,residual.1="conditional")
# ------------------------------------------------------------------------------
# Implementation of Modified CDMC (MCDMC) Methodology under Under HM & HT 
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted.Stratum<-Census.data.fitted[order(Census.data.fitted$Stratum.by.PP.Size, Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]

set.seed(2015)
M3.BCDMC.HM.2L.FGT.Estimate.UNC.UPOVLN<-MCD.MC.HM.2L.FGT.Estimator(beta=beta.gls.2,var.beta=var.beta.gls.2,eta.s=u.gls.2,eps.s=sample.data.fitted$eps.gls.2,
        var.com.2=est.sigma2.2$sigma2.2,var.com.1=est.sigma2.2$sigma2.1,Mod.var.com.2=c(unlist(adj.lemda2.2.K3.PP.i)),NoClusterBlock=c(unlist(No.Cluster.B.PP)),
        ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted.Stratum$AREA.ID,ID.C=Census.data.fitted.Stratum$PSU.ID,
        X.U=as.matrix(x.matrix.U.Stratum),t=Census.data.fitted.Stratum$upovln,HH.Size=Census.data.fitted.Stratum$HH.size.U,No.Boot=5,residual.1=c("unconditional"))

set.seed(2015)
M3.BCDMC.HM.2L.FGT.Estimate.CON.UPOVLN<-MCD.MC.HM.2L.FGT.Estimator(beta=beta.gls.2,var.beta=var.beta.gls.2,eta.s=u.gls.2,eps.s=sample.data.fitted$eps.gls.2,
        var.com.2=est.sigma2.2$sigma2.2,var.com.1=est.sigma2.2$sigma2.1,Mod.var.com.2=c(unlist(adj.lemda2.2.K3.PP.i)),NoClusterBlock=c(unlist(No.Cluster.B.PP)),
        ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted.Stratum$AREA.ID,ID.C=Census.data.fitted.Stratum$PSU.ID,
        X.U=as.matrix(x.matrix.U.Stratum),t=Census.data.fitted.Stratum$upovln,HH.Size=Census.data.fitted.Stratum$HH.size.U,No.Boot=5,residual.1=c("conditional"))

set.seed(2015)
M3.BCDMC.HT.2L.FGT.Estimate.UNC.UPOVLN<-MCD.MC.HT.2L.FGT.Estimator(beta=beta.gls.2.HT.STR,var.beta=var.beta.gls.2.HT.STR,eta.s=u.gls.2.STR,eps.s=sample.data.fitted$eps.gls.2.STR,
        var.com.2=est.sigma2.2.HT$sigma2.2,var.com.1=est.sigma2.2.HT$sigma2.1,Mod.var.com.2=c(unlist(adj.lemda2.2.K3.PP.i.HT)),NoClusterBlock=c(unlist(No.Cluster.B.PP)),
        var.com.HH.s=sample.data.fitted$sig2.ch.hat.2L.MOM,var.com.HH.U=Census.data.fitted.Stratum$sig2.ch.hat.2L.MOM,
        ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted.Stratum$AREA.ID,ID.C=Census.data.fitted.Stratum$PSU.ID,
        X.U=as.matrix(x.matrix.U.Stratum),t=Census.data.fitted.Stratum$upovln,HH.Size=Census.data.fitted.Stratum$HH.size.U,No.Boot=5,residual.1=c("unconditional"))

set.seed(2015)
M3.BCDMC.HT.2L.FGT.Estimate.CON.UPOVLN<-MCD.MC.HT.2L.FGT.Estimator(beta=beta.gls.2.HT.STR,var.beta=var.beta.gls.2.HT.STR,eta.s=u.gls.2.STR,eps.s=sample.data.fitted$eps.gls.2.STR,
       var.com.2=est.sigma2.2.HT$sigma2.2,var.com.1=est.sigma2.2.HT$sigma2.1,Mod.var.com.2=c(unlist(adj.lemda2.2.K3.PP.i.HT)),NoClusterBlock=c(unlist(No.Cluster.B.PP)),
       var.com.HH.s=sample.data.fitted$sig2.ch.hat.2L.MOM,var.com.HH.U=Census.data.fitted.Stratum$sig2.ch.hat.2L.MOM,
       ID.C.s=sample.data.fitted$PSU.ID,ID.D=Census.data.fitted.Stratum$AREA.ID,ID.C=Census.data.fitted.Stratum$PSU.ID,
       X.U=as.matrix(x.matrix.U.Stratum),t=Census.data.fitted.Stratum$upovln,HH.Size=Census.data.fitted.Stratum$HH.size.U,No.Boot=5,residual.1=c("conditional"))

# ------------------------------------------------------------------------------
# Implementation of Modified CDSM (MCDSM) Methodology under Under HM & HT 
# ------------------------------------------------------------------------------
sample.data.fitted<-sample.data.fitted[order(sample.data.fitted$AREA.ID,sample.data.fitted$PSU.ID,sample.data.fitted$HH.ID),]
Census.data.fitted.Stratum<-Census.data.fitted[order(Census.data.fitted$Stratum.by.PP.Size, Census.data.fitted$AREA.ID,Census.data.fitted$PSU.ID,Census.data.fitted$HH.ID),]

set.seed(2015)
M3.BCDSM.HM.2L.FGT.Estimate.FIXED.UPOVLN<-MCD.SM.HM.2L.FGT.Estimator(beta=beta.gls.2,var.beta=var.beta.gls.2,eta.s=as.vector(u.gls.2),eps.s=as.vector(sample.data.fitted$eps.gls.2),
       var.com.2=est.sigma2.2$sigma2.2,var.com.1=est.sigma2.2$sigma2.1,Mod.var.com.2=c(unlist(adj.lemda2.2.K3.PP.i)),NoClusterBlock=c(unlist(No.Cluster.B.PP)),
       Stratum=Census.data.fitted.Stratum$Stratum.by.PP.Size,ID.D=Census.data.fitted.Stratum$AREA.ID,ID.C=Census.data.fitted.Stratum$PSU.ID,ID.HH=Census.data.fitted.Stratum$HH.ID,X.U=as.matrix(x.matrix.U.Stratum),
       t=Census.data.fitted.Stratum$upovln,HH.Size=Census.data.fitted.Stratum$HH.size.U,No.Boot=5,residual.1="Fixed")

set.seed(2015)
M3.BCDSM.HT.2L.FGT.Estimate.Fixed.UPOVLN<-MCD.SM.HT.2L.FGT.Estimator.Scale(beta=beta.gls.2.HT.STR,var.beta=var.beta.gls.2.HT.STR,eta.s=as.vector(u.gls.2.STR),
       eps.s=as.vector(sample.data.fitted$eps.gls.2.STR),var.com.2=est.sigma2.2.HT$sigma2.2,var.com.1=est.sigma2.2.HT$sigma2.1,
       Mod.var.com.2=c(unlist(adj.lemda2.2.K3.PP.i.HT)),NoClusterBlock=c(unlist(No.Cluster.B.PP)),
       var.com.HH.s=as.vector(sample.data.fitted$sig2.ch.hat.2L.MOM),var.com.HH.U=as.vector(Census.data.fitted.Stratum$sig2.ch.hat.2L.MOM),
       Stratum=Census.data.fitted.Stratum$Stratum.by.PP.Size,ID.D=Census.data.fitted.Stratum$AREA.ID,ID.C=Census.data.fitted.Stratum$PSU.ID,ID.HH=Census.data.fitted.Stratum$HH.ID,X.U=as.matrix(x.matrix.U.Stratum),
       t=Census.data.fitted.Stratum$upovln,HH.Size=Census.data.fitted.Stratum$HH.size.U,No.Boot=5,residual.1="Fixed")

# ------------------------------------------------------------------------------
# Divide Survey and Census datasets acording to Clusters residential place
# ------------------------------------------------------------------------------
load("Thesis R Script/Census.data.Rdata")
load("Thesis R Script/Survey.data.Rdata")

# ------------------------------------------------------------------------------
# Population and Sample Data structure 
# ------------------------------------------------------------------------------
N.Area<-tapply.order(Census.data.fitted$hhold,Census.data.fitted$ID.UPZ,length,unique(Census.data.fitted$ID.UPZ))
N.Cluster<-tapply.order(Census.data.fitted$hhold,Census.data.fitted$psu,length,unique(Census.data.fitted$psu))
No.Area<-length(N.Area)
No.Cluster<-length(N.Cluster)
N<-sum(N.Area)
Census.data.fitted$HH.ID<-c(1:N)
Census.data.fitted$PSU.ID<-rep(c(1:No.Cluster),N.Cluster)
Census.data.fitted$AREA.ID<-rep(c(1:No.Area),N.Area)
No.Cluster.s<-length(unique(sample.data.fitted$psu))
n<-length(sample.data.fitted$ln_p_expnd)
n.i<-tapply.order(sample.data.fitted$ln_p_expnd,sample.data.fitted$ID.UPZ,length,unique(sample.data.fitted$ID.UPZ))
n.ij<-tapply.order(sample.data.fitted$ln_p_expnd,sample.data.fitted$psu,length,unique(sample.data.fitted$psu))
No.Area.s<-length(n.i)
sample.data.fitted$HH.ID<-c(1:n)
sample.data.fitted$PSU.ID<-rep(c(1:No.Cluster.s),n.ij)
sample.data.fitted$AREA.ID<-rep(c(1:No.Area.s),n.i)
No.PP.Area.U<-tapply.order(Census.data.fitted$HH.size.U,Census.data.fitted$ID.UPZ,sum,unique(Census.data.fitted$ID.UPZ))

# ------------------------------------------------------------------------------
# Rural and Urban Datasets
# ------------------------------------------------------------------------------
sample.data.fitted.rural.cluster<-subset(sample.data.fitted,sample.data.fitted$rural==1) ; dim(sample.data.fitted.rural.cluster) # 4653   40
sample.data.fitted.urban.cluster<-subset(sample.data.fitted,sample.data.fitted$rural==0) ; dim(sample.data.fitted.urban.cluster) # 2775   40
Census.data.fitted.rural.cluster<-subset(Census.data.fitted,Census.data.fitted$rural==1) ; dim(Census.data.fitted.rural.cluster) # 1013241   40
Census.data.fitted.urban.cluster<-subset(Census.data.fitted,Census.data.fitted$rural==0) ; dim(Census.data.fitted.urban.cluster) #  244849   40
# ------------------------------------------------------------------------------#
# Multilevel model by Residence 
# ------------------------------------------------------------------------------#
sample.data.fitted.rural.cluster<-sample.data.fitted.rural.cluster[order(sample.data.fitted.rural.cluster$AREA.ID,sample.data.fitted.rural.cluster$PSU.ID,sample.data.fitted.rural.cluster$HH.ID),]
sample.data.fitted.urban.cluster<-sample.data.fitted.urban.cluster[order(sample.data.fitted.urban.cluster$AREA.ID,sample.data.fitted.urban.cluster$PSU.ID,sample.data.fitted.urban.cluster$HH.ID),]

Census.data.fitted.rural.cluster<-Census.data.fitted.rural.cluster[order(Census.data.fitted.rural.cluster$AREA.ID,Census.data.fitted.rural.cluster$PSU.ID,Census.data.fitted.rural.cluster$HH.ID),]
Census.data.fitted.urban.cluster<-Census.data.fitted.urban.cluster[order(Census.data.fitted.urban.cluster$AREA.ID,Census.data.fitted.urban.cluster$PSU.ID,Census.data.fitted.urban.cluster$HH.ID),]

# ------------------------------------------------------------------------------
# 2l model using MOM for Rural data set 
# ------------------------------------------------------------------------------
sample.data.fitted.rural.cluster<-sample.data.fitted.rural.cluster[order(sample.data.fitted.rural.cluster$AREA.ID,sample.data.fitted.rural.cluster$PSU.ID,sample.data.fitted.rural.cluster$HH.ID),]
Rural.ols.1<-lm(ln_p_expnd~electric+ilattr_1+ilattr_3+iwater1+ibuild_3+owner*ibuild_4+workst2p+workst3p+
            iincom_3+num_hh+num_hh2+hhhprmed+literatep+child5p+mhhsize+depratio+paginc+idiv_1+idiv_7+
            idiv_4+idiv_5+femalep,data=sample.data.fitted.rural.cluster)
sample.data.fitted.rural.cluster$u.ch<-resid(Rural.ols.1)
Rural.u<-tapply.order(sample.data.fitted.rural.cluster$u.ch,sample.data.fitted.rural.cluster$PSU.ID,mean,unique(sample.data.fitted.rural.cluster$PSU.ID))
sample.data.fitted.rural.cluster$u.2L <- with(sample.data.fitted.rural.cluster, ave(u.ch, PSU.ID, FUN=mean))
sample.data.fitted.rural.cluster$eps.2L<-sample.data.fitted.rural.cluster$u.ch-sample.data.fitted.rural.cluster$u.2L # No application latter
sample.data.fitted.rural.cluster$y.hat.2<-fitted.values(Rural.ols.1)
Rural.est.sigma2.2<-Var.Com.MM.2(sample.data.fitted.rural.cluster$PSU.ID,sample.data.fitted.rural.cluster$HH.ID,Rural.u,sample.data.fitted.rural.cluster$u.ch)
# VPC=
Rural.est.sigma2.2$sigma2.2/(Rural.est.sigma2.2$sigma2.2+Rural.est.sigma2.2$sigma2.1)

Rural.X.ols<-model.matrix(Rural.ols.1)
Rural.gls.lm2<-GLS.EST.2L(sample.data.fitted.rural.cluster$PSU.ID,sample.data.fitted.rural.cluster$HH.ID,Rural.est.sigma2.2$sigma2.2,Rural.est.sigma2.2$sigma2.1,x.matrix=Rural.X.ols,sample.data.fitted.rural.cluster$ln_p_expnd)
Rural.beta.gls.2<-Rural.gls.lm2$beta.gls
Rural.var.beta.gls.2<-Rural.gls.lm2$vcov.beta.gls
Rural.t.beta.gls.2<-Rural.beta.gls.2/sqrt(diag(Rural.var.beta.gls.2))
Rural.p.beta.gls.2<-2*(1-pt(abs(Rural.t.beta.gls.2),n-length(Rural.beta.gls.2)))
Rural.coef.table.beta.gls.2<-round(data.frame(beta.gls.2=Rural.beta.gls.2,SE=sqrt(diag(Rural.var.beta.gls.2)),t=Rural.t.beta.gls.2,prob=Rural.p.beta.gls.2),5)
Rural.R2.gls.lm2.M<-rsquared.lmm.mom(Rural.beta.gls.2,Rural.X.ols,Rural.est.sigma2.2)$R.squared.M
Rural.R2.gls.lm2.C<-rsquared.lmm.mom(Rural.beta.gls.2,Rural.X.ols,Rural.est.sigma2.2)$R.squared.C
sample.data.fitted.rural.cluster$y.hat.gls.2<-Rural.X.ols%*%Rural.beta.gls.2
sample.data.fitted.rural.cluster$u.ch.gls.2<-sample.data.fitted.rural.cluster$ln_p_expnd-sample.data.fitted.rural.cluster$y.hat.gls.2
sample.data.fitted.rural.cluster$u.gls.2<-with(sample.data.fitted.rural.cluster, ave(u.ch.gls.2, PSU.ID, FUN=mean))
sample.data.fitted.rural.cluster$eps.gls.2<-sample.data.fitted.rural.cluster$u.ch.gls.2-sample.data.fitted.rural.cluster$u.gls.2
u.gls.2<-tapply.order(sample.data.fitted.rural.cluster$u.ch.gls.2,sample.data.fitted.rural.cluster$PSU.ID,mean,unique(sample.data.fitted.rural.cluster$PSU.ID))

# ------------------------------------------------------------------------------
# 2l model using MOM for Urban data set
# ------------------------------------------------------------------------------

sample.data.fitted.urban.cluster<-sample.data.fitted.urban.cluster[order(sample.data.fitted.urban.cluster$AREA.ID,sample.data.fitted.urban.cluster$PSU.ID,sample.data.fitted.urban.cluster$HH.ID),]

Urban.ols.1<-lm(ln_p_expnd~electric+ilattr_1+ilattr_3+iwater1+ibuild_3+owner*ibuild_4+workst2p+workst3p+
                  iincom_3+num_hh+num_hh2+hhhprmed+literatep+child5p+mhhsize+depratio+paginc+idiv_1+idiv_7+
                  idiv_4+idiv_5+femalep,data=sample.data.fitted.urban.cluster)
sample.data.fitted.urban.cluster$u.ch<-resid(Urban.ols.1)
Urban.u<-tapply.order(sample.data.fitted.urban.cluster$u.ch,sample.data.fitted.urban.cluster$PSU.ID,mean,unique(sample.data.fitted.urban.cluster$PSU.ID))
sample.data.fitted.urban.cluster$u.2L <- with(sample.data.fitted.urban.cluster, ave(u.ch, PSU.ID, FUN=mean))
sample.data.fitted.urban.cluster$eps.2L<-sample.data.fitted.urban.cluster$u.ch-sample.data.fitted.urban.cluster$u.2L

Urban.est.sigma2.2<-Var.Com.MM.2(sample.data.fitted.urban.cluster$PSU.ID,sample.data.fitted.urban.cluster$HH.ID,Urban.u,sample.data.fitted.urban.cluster$u.ch)
# VPC=
Urban.est.sigma2.2$sigma2.2/(Urban.est.sigma2.2$sigma2.2+Urban.est.sigma2.2$sigma2.1)
Urban.X.ols<-model.matrix(Urban.ols.1)
Urban.gls.lm2<-GLS.EST.2L(sample.data.fitted.urban.cluster$PSU.ID,sample.data.fitted.urban.cluster$HH.ID,Urban.est.sigma2.2$sigma2.2,Urban.est.sigma2.2$sigma2.1,x.matrix=Urban.X.ols,sample.data.fitted.urban.cluster$ln_p_expnd)
Urban.beta.gls.2<-Urban.gls.lm2$beta.gls
Urban.var.beta.gls.2<-Urban.gls.lm2$vcov.beta.gls
Urban.t.beta.gls.2<-Urban.beta.gls.2/sqrt(diag(Urban.var.beta.gls.2))
Urban.p.beta.gls.2<-2*(1-pt(abs(Urban.t.beta.gls.2),n-length(Urban.beta.gls.2)))
Urban.coef.table.beta.gls.2<-round(data.frame(beta.gls.2=Urban.beta.gls.2,SE=sqrt(diag(Urban.var.beta.gls.2)),t=Urban.t.beta.gls.2,prob=Urban.p.beta.gls.2),5)
Urban.R2.gls.lm2.M<-rsquared.lmm.mom(Urban.beta.gls.2,Urban.X.ols,Urban.est.sigma2.2)$R.squared.M
Urban.R2.gls.lm2.C<-rsquared.lmm.mom(Urban.beta.gls.2,Urban.X.ols,Urban.est.sigma2.2)$R.squared.C

# ------------------------------------------------------------------------------
# 3l model using MOM for Urban data set
# ------------------------------------------------------------------------------
sample.data.fitted.urban.cluster<-sample.data.fitted.urban.cluster[order(sample.data.fitted.urban.cluster$AREA.ID,sample.data.fitted.urban.cluster$PSU.ID,sample.data.fitted.urban.cluster$HH.ID),]
Urban.ols.1<-lm(ln_p_expnd~electric+ilattr_1+ilattr_3+iwater1+ibuild_3+owner*ibuild_4+workst2p+workst3p+
                  iincom_3+num_hh+num_hh2+hhhprmed+literatep+child5p+mhhsize+depratio+paginc+idiv_1+idiv_7+
                  idiv_4+idiv_5+femalep,data=sample.data.fitted.urban.cluster)
sample.data.fitted.urban.cluster$u.ch<-resid(Urban.ols.1)
Urban.u<-tapply.order(sample.data.fitted.urban.cluster$u.ch,sample.data.fitted.urban.cluster$PSU.ID,mean,unique(sample.data.fitted.urban.cluster$PSU.ID))
Urban.eta<-tapply.order(sample.data.fitted.urban.cluster$u.ch,sample.data.fitted.urban.cluster$AREA.ID,mean,unique(sample.data.fitted.urban.cluster$AREA.ID))
sample.data.fitted.urban.cluster$u.3L <- with(sample.data.fitted.urban.cluster, ave(u.ch, PSU.ID, FUN=mean))
sample.data.fitted.urban.cluster$eta.3L<-with(sample.data.fitted.urban.cluster, ave(u.ch, AREA.ID, FUN=mean))
sample.data.fitted.urban.cluster$eps.3L<-sample.data.fitted.urban.cluster$u.ch-sample.data.fitted.urban.cluster$u.3L-sample.data.fitted.urban.cluster$eta.3L # No application latter
Urban.est.sigma2.3<-Var.Com.MM.3(sample.data.fitted.urban.cluster$AREA.ID,sample.data.fitted.urban.cluster$PSU.ID,sample.data.fitted.urban.cluster$HH.ID,Urban.eta,Urban.u,sample.data.fitted.urban.cluster$u.ch)
# VPC=
Urban.est.sigma2.3$sigma2.3/(Urban.est.sigma2.3$sigma2.3+Urban.est.sigma2.3$sigma2.2+Urban.est.sigma2.3$sigma2.1)
Urban.est.sigma2.3$sigma2.2/(Urban.est.sigma2.3$sigma2.3+Urban.est.sigma2.3$sigma2.2+Urban.est.sigma2.3$sigma2.1)
Urban.X.ols<-model.matrix(Urban.ols.1)
Urban.gls.lm3<-GLS.EST.3L(sample.data.fitted.urban.cluster$AREA.ID,sample.data.fitted.urban.cluster$PSU.ID,sample.data.fitted.urban.cluster$HH.ID,Urban.est.sigma2.3$sigma2.3,Urban.est.sigma2.3$sigma2.2,Urban.est.sigma2.3$sigma2.1,x.matrix=Urban.X.ols,sample.data.fitted.urban.cluster$ln_p_expnd)
Urban.beta.gls.3<-Urban.gls.lm3$beta.gls
Urban.var.beta.gls.3<-Urban.gls.lm3$vcov.beta.gls
Urban.t.beta.gls.3<-Urban.beta.gls.3/sqrt(diag(Urban.var.beta.gls.3))
Urban.p.beta.gls.3<-2*(1-pt(abs(Urban.t.beta.gls.3),n-length(Urban.beta.gls.3)))
Urban.coef.table.beta.gls.3<-round(data.frame(beta.gls.3=Urban.beta.gls.3,SE=sqrt(diag(Urban.var.beta.gls.3)),t=Urban.t.beta.gls.3,prob=Urban.p.beta.gls.3),5)
Urban.R2.gls.lm3.M<-rsquared.lmm.mom(Urban.beta.gls.3,Urban.X.ols,Urban.est.sigma2.3)$R.squared.M
Urban.R2.gls.lm3.C<-rsquared.lmm.mom(Urban.beta.gls.3,Urban.X.ols,Urban.est.sigma2.3)$R.squared.C

# ------------------------------------------------------------------------------
# Implementation of the MIXED Model via ELL Methodology
# ------------------------------------------------------------------------------
length(unique(Census.data.fitted.rural.cluster$PSU.ID)) # 10403
length(unique(Census.data.fitted.urban.cluster$PSU.ID)) #  2506

Census.data.fitted.rural.cluster<-Census.data.fitted.rural.cluster[order(Census.data.fitted.rural.cluster$AREA.ID,Census.data.fitted.rural.cluster$PSU.ID,Census.data.fitted.rural.cluster$HH.ID),]
Rural.x.matrix.U<-data.frame(Census.data.fitted.rural.cluster$electric,Census.data.fitted.rural.cluster$ilattr_1,Census.data.fitted.rural.cluster$ilattr_3,Census.data.fitted.rural.cluster$iwater1,Census.data.fitted.rural.cluster$ibuild_3,
         Census.data.fitted.rural.cluster$owner,Census.data.fitted.rural.cluster$ibuild_4,Census.data.fitted.rural.cluster$workst2p,Census.data.fitted.rural.cluster$workst3p,Census.data.fitted.rural.cluster$iincom_3,
         Census.data.fitted.rural.cluster$num_hh,Census.data.fitted.rural.cluster$num_hh2,Census.data.fitted.rural.cluster$hhhprmed,Census.data.fitted.rural.cluster$literatep,Census.data.fitted.rural.cluster$child5p,
         Census.data.fitted.rural.cluster$mhhsize,Census.data.fitted.rural.cluster$depratio,Census.data.fitted.rural.cluster$paginc,Census.data.fitted.rural.cluster$idiv_1,
         Census.data.fitted.rural.cluster$idiv_7,Census.data.fitted.rural.cluster$idiv_4,Census.data.fitted.rural.cluster$idiv_5,Census.data.fitted.rural.cluster$femalep,
         Census.data.fitted.rural.cluster$owner*Census.data.fitted.rural.cluster$ibuild_4)
dim(Rural.x.matrix.U)

Census.data.fitted.urban.cluster<-Census.data.fitted.urban.cluster[order(Census.data.fitted.urban.cluster$AREA.ID,Census.data.fitted.urban.cluster$PSU.ID,Census.data.fitted.urban.cluster$HH.ID),]
Urban.x.matrix.U<-data.frame(Census.data.fitted.urban.cluster$electric,Census.data.fitted.urban.cluster$ilattr_1,Census.data.fitted.urban.cluster$ilattr_3,Census.data.fitted.urban.cluster$iwater1,Census.data.fitted.urban.cluster$ibuild_3,
        Census.data.fitted.urban.cluster$owner,Census.data.fitted.urban.cluster$ibuild_4,Census.data.fitted.urban.cluster$workst2p,Census.data.fitted.urban.cluster$workst3p,Census.data.fitted.urban.cluster$iincom_3,
        Census.data.fitted.urban.cluster$num_hh,Census.data.fitted.urban.cluster$num_hh2,Census.data.fitted.urban.cluster$hhhprmed,Census.data.fitted.urban.cluster$literatep,Census.data.fitted.urban.cluster$child5p,
        Census.data.fitted.urban.cluster$mhhsize,Census.data.fitted.urban.cluster$depratio,Census.data.fitted.urban.cluster$paginc,Census.data.fitted.urban.cluster$idiv_1,
        Census.data.fitted.urban.cluster$idiv_7,Census.data.fitted.urban.cluster$idiv_4,Census.data.fitted.urban.cluster$idiv_5,Census.data.fitted.urban.cluster$femalep,
        Census.data.fitted.urban.cluster$owner*Census.data.fitted.urban.cluster$ibuild_4)
dim(Urban.x.matrix.U)

set.seed(2015)
Mixed.ELL.PB.HM.UPOVLN<-Mixed.ELL.PB.HM.2L.3L.FGT.Estimator(beta.2l=Rural.beta.gls.2,var.beta.2l=Rural.var.beta.gls.2,var.com.1.2l=Rural.est.sigma2.2$sigma2.1,var.com.2.2l=Rural.est.sigma2.2$sigma2.2,
        ID.D.2l=Census.data.fitted.rural.cluster$AREA.ID,ID.C.2l=Census.data.fitted.rural.cluster$PSU.ID,X.U.2l=as.matrix(Rural.x.matrix.U),
        t.2l=Census.data.fitted.rural.cluster$upovln,HH.Size.2l=Census.data.fitted.rural.cluster$HH.size.U,
        beta.3l=Urban.beta.gls.3,var.beta.3l=Urban.var.beta.gls.3,var.com.1.3l=Urban.est.sigma2.3$sigma2.1,var.com.2.3l=Urban.est.sigma2.3$sigma2.2,
        var.com.3.3l=Urban.est.sigma2.3$sigma2.3,ID.D.3l=Census.data.fitted.urban.cluster$AREA.ID,ID.C.3l=Census.data.fitted.urban.cluster$PSU.ID,X.U.3l=as.matrix(Urban.x.matrix.U),
        t.3l=Census.data.fitted.urban.cluster$upovln,HH.Size.3l=Census.data.fitted.urban.cluster$HH.size.U,No.Boot=5)
# ------------------------------------------------------------------------------
# The Work for Multiple cluster are done as the whole dataset not include here
# End the Script for Chapter Six
# ------------------------------------------------------------------------------
