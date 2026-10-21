-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_dimensionBound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.dimensionBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:58:39.694637+00:00
-- url     : https://prove2.me/theorems/797b2aaa-8de9-40f6-bc7c-1260c283173a
-- title:
--   Dimension bound
-- statement:
--   All systems are finite-dimensional and nonzero, with fixed orthonormal product bases, and logarithms are base two. States are positive semidefinite matrices of trace one. For a positive bipartite operator $s$, define $\gamma(s)$ as the infimum of $\operatorname{Tr}(K_A\otimes L_B)$ over Hermitian $K_A,L_B,V_{AB}$ satisfying $T_B(V_{AB}\pm s)\ge0$ and $K_A\otimes L_B\pm V_{AB}\ge0$, with both signs required. Here $T_B$ transposes only Bob's system. Set $C_\gamma(s)=\log_2\gamma(s)$, with $\log_2 0=-\infty$.
--
--   Let $D$ be a dimension-compatible extended-real generalized divergence satisfying data processing for every CPTP channel, $D(r\|cs)=D(r\|s)-\log_2c$ for $c>0$, and $D(r\|r)=0$. Comparisons need not be normalized and divergence values are not truncated to be nonnegative. Write
--   $$\Gamma_D(r)=\inf_{s\ge0:\,\gamma(s)\le1}D(r\|s).$$
--
--   For every state $r_{AB}$, with local dimensions $d_A=\dim A$ and $d_B=\dim B$,
--   $$\Gamma_D(r)\le C_\gamma(r)\le\log_2\min\{d_A,d_B\}.$$
--
--   No full-rank condition is imposed on $r$ or its marginals. This gives an upper bound using the smaller local dimension.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 3, Proposition 5, (15)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Proposition 5, PDF p.3, (15), Appendix D p.9; singular marginals are allowed. -/
theorem dimensionBound (D : Divergence) (hD : IsGeneralizedDivergence D)
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho) :
    capitalGamma D rho ≤ cGamma rho ∧
      cGamma rho ≤ (Real.logb 2 (min (Fintype.card A) (Fintype.card B) : ℕ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
