-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_classicalCommunicationBound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.classicalCommunicationBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:00:08.003198+00:00
-- url     : https://prove2.me/theorems/a7bf53d7-3443-4491-873c-530d5c1740d6
-- title:
--   Classical communication bound
-- statement:
--   All systems are finite-dimensional and nonzero, with fixed orthonormal product bases, and logarithms are base two. States are positive semidefinite matrices of trace one. For a positive bipartite operator $s$, define $\gamma(s)$ as the infimum of $\operatorname{Tr}(K_A\otimes L_B)$ over Hermitian $K_A,L_B,V_{AB}$ satisfying $T_B(V_{AB}\pm s)\ge0$ and $K_A\otimes L_B\pm V_{AB}\ge0$, with both signs required. Here $T_B$ transposes only Bob's system. Set $C_\gamma(s)=\log_2\gamma(s)$, with $\log_2 0=-\infty$.
--
--   Let $D$ be a dimension-compatible extended-real generalized divergence satisfying data processing for every CPTP channel, $D(r\|cs)=D(r\|s)-\log_2c$ for $c>0$, and $D(r\|r)=0$. Comparisons need not be normalized and divergence values are not truncated to be nonnegative. Write
--   $$\Gamma_D(r)=\inf_{s\ge0:\,\gamma(s)\le1}D(r\|s).$$
--
--   Let $X$ be a nonempty finite alphabet of size $d_X$, let $p(x)\ge0$ with $\sum_xp(x)=1$, and let $r^x_{AB}$ be states. Form the same operator $r_{XAB}=\sum_xp(x)|x\rangle\langle x|\otimes r^x_{AB}$ in the two tensor-factor orderings. Then
--   $$C_\gamma^{AX:B}(r)\le\log_2d_X+C_\gamma^{A:BX}(r),\qquad
--   \Gamma_D^{AX:B}(r)\le\log_2d_X+\Gamma_D^{A:BX}(r).$$
--
--   No independence or strict positivity of $p(x)$ is needed. This bounds the increase from moving a classical register by its full alphabet charge.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 3, Proposition 7, (17)–(19)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Proposition 7, PDF p.3, (17)–(19), Appendix E pp.9–10.
The cost is the full alphabet dimension, without independence or positive-probability assumptions. -/
theorem classicalCommunicationBound (D : Divergence) (hD : IsGeneralizedDivergence D)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (rho : X → Matrix (A × B) (A × B) ℂ)
    (hrho : ∀ x, QAlgorithms.IsDensityMatrix (rho x)) :
    cGamma (cqLeft p rho) ≤ (Real.logb 2 (Fintype.card X) : EReal) + cGamma (cqRight p rho) ∧
    capitalGamma D (cqLeft p rho) ≤ (Real.logb 2 (Fintype.card X) : EReal) +
      capitalGamma D (cqRight p rho) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
