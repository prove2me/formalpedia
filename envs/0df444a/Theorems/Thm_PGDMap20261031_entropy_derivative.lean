-- Prove2me | Theorems.Thm_PGDMap20261031_entropy_derivative
-- name    : PGDMap20261031.entropy_derivative
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:03:58.614537+00:00
-- url     : https://prove2.me/theorems/afd62a10-003b-4b41-a3b1-6e094d509fe3
-- title:
--   The derivative of the positive entropy-mixture objective
-- statement:
--   ## Statement
--
--   A mixture $M$ consists of an integer $m\ge 1$, real numbers $a_j,w_j$ indexed by $j\in\{0,\ldots,m-1\}$, and a real number $\lambda$, with $0<a_j<1$, $w_j>0$ for every $j$, and $\lambda>0$; no condition $\sum_j w_j=1$ is imposed. For every real $t$, write $H(t)=\big((1+t)\log(1+t)+(1-t)\log(1-t)\big)/2$, using the total real logarithm of the code. Define $F_M(t)=\sum_{j=0}^{m-1}w_j H(\sqrt{a_j}\,t)$ for real $t$. For real $\ell,t$, let $f_{M,\ell}(t)=F_M(t)+\lambda H(t)+\ell t$ and let $G_{M,\ell}(t)$ be the actual total derivative operator $\operatorname{deriv}(f_{M,\ell})(t)$ used in the code. For every real $t$, write $U(t)=\big(\log(1+t)-\log(1-t)\big)/2$, using the total real logarithm of the code. Define $S_M(t)=\sum_{j=0}^{m-1}w_j\sqrt{a_j}\,U(\sqrt{a_j}\,t)$ for real $t$. The theorem asserts the following. For every mixture $M$, every real $\ell$, and every real $t$ with $-1<t<1$, the actual derivative satisfies $G_{M,\ell}(t)=S_M(t)+\lambda U(t)+\ell$.
-- source:
--   Jointly Optimal Bregman Geometry and Stepsize for Positive Entropy Mixtures, manuscript dated 2026-10-30, definitions p. 1; Lemma 1 proof p. 2; local source: 03_Jointly_Optimal_Bregman_Map_and_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Entropy
open PGDMap20261031

theorem PGDMap20261031.entropy_derivative : EntropyDerivativeClaim := by sorry
