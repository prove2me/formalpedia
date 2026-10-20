-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_oneShotLoccBound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.oneShotLoccBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:03:31.867904+00:00
-- url     : https://prove2.me/theorems/ecdfc179-6a6d-4f81-9b93-fc773d8c9713
-- title:
--   One-shot LOCC randomness upper bound
-- statement:
--   All systems are finite-dimensional and nonzero, with fixed orthonormal product bases, and logarithms are base two. States are positive semidefinite matrices of trace one. For a positive bipartite operator $s$, define $\gamma(s)$ as the infimum of $\operatorname{Tr}(K_A\otimes L_B)$ over Hermitian $K_A,L_B,V_{AB}$ satisfying $T_B(V_{AB}\pm s)\ge0$ and $K_A\otimes L_B\pm V_{AB}\ge0$, with both signs required. Here $T_B$ transposes only Bob's system. Set $C_\gamma(s)=\log_2\gamma(s)$, with $\log_2 0=-\infty$.
--
--   For a state $r_{AB}$, let $R^\varepsilon_\to(r)$ and $R^\varepsilon_\leftrightarrow(r)$ be the suprema of $\log_2d-\sum_i\log_2|L_i|$ over, respectively, Alice-to-Bob and arbitrary finite-round LOCC protocols. Each protocol uses local CPTP operations, finite classical messages $L_i$, arbitrary finite local memories, and no free shared seed. Its final classical state $w$ must satisfy $F(w,\bar\Phi_d)\ge1-\varepsilon$, where $F$ is squared fidelity and $\bar\Phi_d=d^{-1}\sum_{x=0}^{d-1}|xx\rangle\langle xx|$. Every alphabet size and $d$ is positive; unused symbols still contribute to the communication charge.
--
--   For $\alpha>1$, write $\widetilde D_\alpha(r\|s)=(\alpha-1)^{-1}\log_2\operatorname{Tr}[(s^{(1-\alpha)/(2\alpha)}r s^{(1-\alpha)/(2\alpha)})^\alpha]$, with $+\infty$ when $\operatorname{supp}r\nsubseteq\operatorname{supp}s$, and set $\widetilde\Gamma_\alpha=\Gamma_{\widetilde D_\alpha}$.
--
--   For $0\le\varepsilon<1$, the penalty is $p_\alpha(\varepsilon)=\frac{\alpha}{\alpha-1}\log_2\frac1{1-\varepsilon}$; set $p_\alpha(1)=+\infty$.
--
--   For every state $r_{AB}$, $0\le\varepsilon\le1$, and $\alpha>1$,
--   $$R^\varepsilon_\leftrightarrow(r)\le\widetilde\Gamma_\alpha(r)+p_\alpha(\varepsilon).$$
--
--   The number of communication rounds ranges over all finite values. This is a one-shot converse, with the infinite endpoint at error one.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 4, Theorem 11, (40)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Theorem 11, PDF p.4, (40): one-shot bound over arbitrary finite numbers of
LOCC rounds, with the extended epsilon=1 endpoint. -/
theorem oneShotLoccBound (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) (eps alpha : ℝ)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) (halpha : 1 < alpha) :
    oneShot true eps rho ≤ capitalGamma (sandwiched alpha) rho + errorPenalty alpha eps := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
