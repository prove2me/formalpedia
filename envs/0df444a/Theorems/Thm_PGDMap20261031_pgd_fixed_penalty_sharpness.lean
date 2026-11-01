-- Prove2me | Theorems.Thm_PGDMap20261031_pgd_fixed_penalty_sharpness
-- name    : PGDMap20261031.pgd_fixed_penalty_sharpness
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:03:59.786048+00:00
-- url     : https://prove2.me/theorems/643d7ce9-77b0-4329-876e-23be7639a087
-- title:
--   Matching lower bounds for every fixed penalty
-- statement:
--   ## Statement
--
--   Let $d\in\mathbb N$, including $d=0$, and let $E=\mathbb R^d$ with its Euclidean inner product and norm. A penalty datum is an arbitrary set $D\subseteq E$ and a total function $\rho:E\to\mathbb R$. Call it admissible when $D$ is nonempty, its epigraph $\{(z,a)\in E\times\mathbb R:z\in D,\ \rho(z)\le a\}$ is closed, and $\rho$ is convex on the convex set $D$. For $\eta\in\mathbb R$, say that $\rho$ has modulus $\eta$ on $D$ when, for all $a,b\in D$ and all real $t\in[0,1]$, $\rho(ta+(1-t)b)\le t\rho(a)+(1-t)\rho(b)-(\eta/2)t(1-t)\|a-b\|^2$. Write $m=\sup\{\eta\in\mathbb R:0\le\eta\ \text{and }\rho\text{ has modulus }\eta\text{ on }D\}$, using the total real supremum operation, whose value is $0$ for an empty or unbounded-above set. For a real $L$, a pair of total functions $f:E\to\mathbb R$ and $g:E\to E$ is $L$-smooth convex here when $f$ is convex on all of $E$, $f$ has gradient $g(z)$ at every $z\in E$, and $\|g(a)-g(b)\|\le L\|a-b\|$ for every $a,b\in E$. For real $\gamma$, natural $n$, and a sequence $x:\mathbb N\to E$, the trajectory condition through $n$ means that $x_i\in D$ for every natural $i\le n$, and that, for every natural $i<n$ and every $y\in D$, $\rho(x_{i+1})+\|x_{i+1}-(x_i-\gamma g(x_i))\|^2/(2\gamma)\le\rho(y)+\|y-(x_i-\gamma g(x_i))\|^2/(2\gamma)$. No condition is imposed on indices above $n$. Set $\Delta_n=f(x_0)+\rho(x_0)-f(x_n)-\rho(x_n)$ and $R_n(\gamma)=\|x_{n-1}-x_n\|^2/\gamma^2$, where $n-1$ is truncated to $0$ at $n=0$ and real division by zero is $0$. For fixed $D,\rho,L,h,N$, let $\mathcal R(D,\rho;L,h,N)$ be the set of real numbers $R_N(h/L)/(L\Delta_N)$ obtained from some total $f:E\to\mathbb R$, $g:E\to E$, and $x:\mathbb N\to E$ such that $f,g$ are $L$-smooth convex in the stated sense, the trajectory condition holds through $N$ with $\gamma=h/L$, and $\Delta_N>0$. For $N\in\mathbb N$ (including $0$) and $h,q\in\mathbb R$, put $b=1+hq$, define $A_N(h,q)=2/[h(2N-h)]$ if $q=0$ and $A_N(h,q)=2q/[b^{2N}-1-h^2q]$ otherwise, define $B_N(h,q)=2(1+q)(1-h)^{\,2N-2}/[b^{2N}-(1-h)^{2N}]$, and define $C_N(h,q)=2/[h(2-h+hq)]$ when $N=1$ and $C_N(h,q)=\max\{A_N(h,q),B_N(h,q)\}$ otherwise. The exponent $2N-2$ in $B_N$ uses subtraction in $\mathbb N$, so it is $0$ when $N=0$ or $N=1$. Every division is division in $\mathbb R$, with division by zero equal to zero. For every natural $d,N$, admissible $(D,\rho)$ on $E=\mathbb R^d$ with two distinct domain points, and real $L>0$ and $h$ with $0<h<2$ and $N\ge1$, for every real $\varepsilon>0$ there exists $v\in\mathcal R(D,\rho;L,h,N)$ such that $C_N(h,m/L)-\varepsilon<v$. The conclusion is a strict lower approximation and does not by itself assert an upper bound for the members of $\mathcal R$.
-- source:
--   Exact Residual Curves for Proximal Gradient Descent with a Fixed Penalty, manuscript dated 2026-10-30, Theorem 1 proof, p. 7; local source: 01_PGD_Exact_Residual_Curve.pdf

import Definitions.Def_PGDMap20261031_PGD
open PGDMap20261031

theorem PGDMap20261031.pgd_fixed_penalty_sharpness : FixedPenaltySharpnessClaim := by sorry
