-- Prove2me | Theorems.Thm_PGDMap20261031_pgd_uniform_upper
-- name    : PGDMap20261031.pgd_uniform_upper
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:03:59.104904+00:00
-- url     : https://prove2.me/theorems/67fddcd9-15e1-449b-ad65-de0142011a21
-- title:
--   Uniform terminal-residual bound
-- statement:
--   ## Statement
--
--   Let $d\in\mathbb N$, including $d=0$, and let $E=\mathbb R^d$ with its Euclidean inner product and norm. A penalty datum is an arbitrary set $D\subseteq E$ and a total function $\rho:E\to\mathbb R$. Call it admissible when $D$ is nonempty, its epigraph $\{(z,a)\in E\times\mathbb R:z\in D,\ \rho(z)\le a\}$ is closed, and $\rho$ is convex on the convex set $D$. For $\eta\in\mathbb R$, say that $\rho$ has modulus $\eta$ on $D$ when, for all $a,b\in D$ and all real $t\in[0,1]$, $\rho(ta+(1-t)b)\le t\rho(a)+(1-t)\rho(b)-(\eta/2)t(1-t)\|a-b\|^2$. For a real $L$, a pair of total functions $f:E\to\mathbb R$ and $g:E\to E$ is $L$-smooth convex here when $f$ is convex on all of $E$, $f$ has gradient $g(z)$ at every $z\in E$, and $\|g(a)-g(b)\|\le L\|a-b\|$ for every $a,b\in E$. For real $\gamma$, natural $n$, and a sequence $x:\mathbb N\to E$, the trajectory condition through $n$ means that $x_i\in D$ for every natural $i\le n$, and that, for every natural $i<n$ and every $y\in D$, $\rho(x_{i+1})+\|x_{i+1}-(x_i-\gamma g(x_i))\|^2/(2\gamma)\le\rho(y)+\|y-(x_i-\gamma g(x_i))\|^2/(2\gamma)$. No condition is imposed on indices above $n$. Set $\Delta_n=f(x_0)+\rho(x_0)-f(x_n)-\rho(x_n)$ and $R_n(\gamma)=\|x_{n-1}-x_n\|^2/\gamma^2$, where $n-1$ is truncated to $0$ at $n=0$ and real division by zero is $0$. For $N\in\mathbb N$ (including $0$) and $h,q\in\mathbb R$, put $b=1+hq$, define $A_N(h,q)=2/[h(2N-h)]$ if $q=0$ and $A_N(h,q)=2q/[b^{2N}-1-h^2q]$ otherwise, define $B_N(h,q)=2(1+q)(1-h)^{\,2N-2}/[b^{2N}-(1-h)^{2N}]$, and define $C_N(h,q)=2/[h(2-h+hq)]$ when $N=1$ and $C_N(h,q)=\max\{A_N(h,q),B_N(h,q)\}$ otherwise. The exponent $2N-2$ in $B_N$ uses subtraction in $\mathbb N$, so it is $0$ when $N=0$ or $N=1$. Every division is division in $\mathbb R$, with division by zero equal to zero. For every natural $d,N$, penalty datum $(D,\rho)$ on $E=\mathbb R^d$, real $L,\mu,h$, total $f:E\to\mathbb R$, $g:E\to E$, and $x:\mathbb N\to E$, if $(D,\rho)$ is admissible, $L>0$, $\mu\ge0$, $\rho$ has modulus $\mu$ on $D$, $0<h<2$, $N\ge1$, $f,g$ are $L$-smooth convex, and the trajectory condition holds through $N$ with $\gamma=h/L$, then $R_N(h/L)\le L C_N(h,\mu/L)\Delta_N$. There is no premise that $\Delta_N$ is positive, that $D$ contains distinct points, or that $\mu$ is the supremal modulus.
-- source:
--   Exact Residual Curves for Proximal Gradient Descent with a Fixed Penalty, manuscript dated 2026-10-30, Theorem 1, p. 1; local source: 01_PGD_Exact_Residual_Curve.pdf

import Definitions.Def_PGDMap20261031_PGD
open PGDMap20261031

theorem PGDMap20261031.pgd_uniform_upper : UniformUpperClaim := by sorry
