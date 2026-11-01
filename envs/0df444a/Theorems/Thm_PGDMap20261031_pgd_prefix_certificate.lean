-- Prove2me | Theorems.Thm_PGDMap20261031_pgd_prefix_certificate
-- name    : PGDMap20261031.pgd_prefix_certificate
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:04:00.334015+00:00
-- url     : https://prove2.me/theorems/664039ab-8046-441b-b64d-f4698817f7f3
-- title:
--   Lemma 1: a nonnegative prefix certificate
-- statement:
--   ## Statement
--
--   Let $d\in\mathbb N$, including $d=0$, and let $E=\mathbb R^d$ with its Euclidean inner product and norm. A penalty datum is an arbitrary set $D\subseteq E$ and a total function $\rho:E\to\mathbb R$. Call it admissible when $D$ is nonempty, its epigraph $\{(z,a)\in E\times\mathbb R:z\in D,\ \rho(z)\le a\}$ is closed, and $\rho$ is convex on the convex set $D$. For $\eta\in\mathbb R$, say that $\rho$ has modulus $\eta$ on $D$ when, for all $a,b\in D$ and all real $t\in[0,1]$, $\rho(ta+(1-t)b)\le t\rho(a)+(1-t)\rho(b)-(\eta/2)t(1-t)\|a-b\|^2$. For a real $L$, a pair of total functions $f:E\to\mathbb R$ and $g:E\to E$ is $L$-smooth convex here when $f$ is convex on all of $E$, $f$ has gradient $g(z)$ at every $z\in E$, and $\|g(a)-g(b)\|\le L\|a-b\|$ for every $a,b\in E$. For real $\gamma$, natural $n$, and a sequence $x:\mathbb N\to E$, the trajectory condition through $n$ means that $x_i\in D$ for every natural $i\le n$, and that, for every natural $i<n$ and every $y\in D$, $\rho(x_{i+1})+\|x_{i+1}-(x_i-\gamma g(x_i))\|^2/(2\gamma)\le\rho(y)+\|y-(x_i-\gamma g(x_i))\|^2/(2\gamma)$. No condition is imposed on indices above $n$. Set $\Delta_n=f(x_0)+\rho(x_0)-f(x_n)-\rho(x_n)$ and $R_n(\gamma)=\|x_{n-1}-x_n\|^2/\gamma^2$, where $n-1$ is truncated to $0$ at $n=0$ and real division by zero is $0$. For natural $k$, put $S_k(z)=\sum_{j=1}^{2k}(z^j)^{-1}$ (the empty sum is $0$ at $k=0$, and $0^{-1}=0$), $b=1+hq$, and $P_k(h,q)=\frac{b}{2h}S_k(1/b)$ when $h=1$, while $P_k(h,q)=\frac{b}{2h}\min\{S_k(1/b),S_k((1-h)/b)\}$ when $h\ne1$. For every natural $d,k$, penalty datum $(D,\rho)$ on $E=\mathbb R^d$, real $q,h$, total $f:E\to\mathbb R$, $g:E\to E$, and $x:\mathbb N\to E$, if $(D,\rho)$ is admissible, $q\ge0$, $\rho$ has modulus $q$ on $D$, $0<h<2$, $k\ge1$, $f,g$ are $1$-smooth convex, and the trajectory condition holds through $k+1$ with $\gamma=h$, then $P_k(h,q)\|x_k-x_{k+1}\|^2\le\Delta_k$. Thus the squared step on the left is the step from $k$ to $k+1$, while the decrease on the right ends at $k$.
-- source:
--   Exact Residual Curves for Proximal Gradient Descent with a Fixed Penalty, manuscript dated 2026-10-30, Lemma 1, pp. 2-5; local source: 01_PGD_Exact_Residual_Curve.pdf

import Definitions.Def_PGDMap20261031_PGD
open PGDMap20261031

theorem PGDMap20261031.pgd_prefix_certificate : PrefixCertificateClaim := by sorry
