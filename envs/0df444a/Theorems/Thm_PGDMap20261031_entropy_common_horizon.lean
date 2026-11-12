-- Prove2me | Theorems.Thm_PGDMap20261031_entropy_common_horizon
-- name    : PGDMap20261031.entropy_common_horizon
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:04:03.82098+00:00
-- url     : https://prove2.me/theorems/68bca083-d964-4bd8-8ae6-979f966ecb28
-- title:
--   One joint optimum for every finite iteration horizon
-- statement:
--   ## Statement
--
--   A mixture $M$ consists of an integer $m\ge 1$, real numbers $a_j,w_j$ indexed by $j\in\{0,\ldots,m-1\}$, and a real number $\lambda$, with $0<a_j<1$, $w_j>0$ for every $j$, and $\lambda>0$; no condition $\sum_j w_j=1$ is imposed. For real $c,t$, define $Q_c(t)=\big((1+t)^{-c}+(1-t)^{-c}\big)/2$, where powers are the code's total real-power operation. For real $t$, let $C_M(t)=\sum_{j=0}^{m-1}w_j a_j/(1-a_jt^2)$ and $D_M(t)=\lambda/(1-t^2)$; for real $c,p,t$, let $e_{M,c,p}(t)=\big(pQ_c(t)-C_M(t)\big)/\big(pQ_c(t)+D_M(t)\big)$, with total real division. Let $E_M(c,p)=\{|e_{M,c,p}(t)|:0\le t<1\}$ and $r_M(c,p)=\operatorname{sSup}_{\mathbb R}E_M(c,p)$, the total real supremum operation, which uses its library default on an empty or unbounded-above set. A pair $(c,p)\in\mathbb R^2$ is admissible exactly when $0\le c\le2$ and $p>0$. A pair $z=(c,p)$ is an optimum for $M$ exactly when it is admissible and $r_M(c,p)\le r_M(d,q)$ for every admissible pair $(d,q)$. For real $c,t$, define $h_c(t)=\int_0^t Q_c(s)\,ds$, the oriented interval integral with respect to Lebesgue measure. For every real $t$, write $U(t)=\big(\log(1+t)-\log(1-t)\big)/2$, using the total real logarithm of the code. Define $S_M(t)=\sum_{j=0}^{m-1}w_j\sqrt{a_j}\,U(\sqrt{a_j}\,t)$ for real $t$. For real $c,p,\ell$, a natural number $N$ (possibly zero), and a sequence $x:\mathbb N\to\mathbb R$, an $N$-step trajectory means that $-1<x_i<1$ for every natural number $i\le N$, and that $p h_c(x_{i+1})+\lambda U(x_{i+1})=p h_c(x_i)-S_M(x_i)-\ell$ for every natural number $i<N$; no condition is placed on $x_i$ for $i>N$. For every real $t$, write $H(t)=\big((1+t)\log(1+t)+(1-t)\log(1-t)\big)/2$, using the total real logarithm of the code. Define $F_M(t)=\sum_{j=0}^{m-1}w_j H(\sqrt{a_j}\,t)$ for real $t$. For real $\ell,t$, let $f_{M,\ell}(t)=F_M(t)+\lambda H(t)+\ell t$ and let $G_{M,\ell}(t)$ be the actual total derivative operator $\operatorname{deriv}(f_{M,\ell})(t)$ used in the code. For real $c,p$ and natural $N$, let $P_M(c,p,N)$ be the set of all real numbers $|G_{M,\ell}(x_N)|^2/|G_{M,\ell}(x_0)|^2$ obtained from some real $\ell$ and some $N$-step trajectory $x$ with $G_{M,\ell}(x_0)\ne0$; let $\Omega_M(c,p,N)=\operatorname{sSup}_{\mathbb R}P_M(c,p,N)$, using the total real supremum operation even when the set is empty or unbounded above. The theorem asserts the following. For every mixture $M$, every natural number $N\ge1$, and every real pair $z=(c,p)$ that is an optimum for $M$, $\Omega_M(c,p,N)\le\Omega_M(d,q,N)$ for every admissible pair $(d,q)$, and every admissible pair $(d,q)$ with $\Omega_M(d,q,N)=\Omega_M(c,p,N)$ equals $(c,p)$.
-- source:
--   Jointly Optimal Bregman Geometry and Stepsize for Positive Entropy Mixtures, manuscript dated 2026-10-30, Theorem 1(4), p. 2; local source: 03_Jointly_Optimal_Bregman_Map_and_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Entropy
open PGDMap20261031

theorem PGDMap20261031.entropy_common_horizon : CommonFiniteHorizonClaim := by sorry
