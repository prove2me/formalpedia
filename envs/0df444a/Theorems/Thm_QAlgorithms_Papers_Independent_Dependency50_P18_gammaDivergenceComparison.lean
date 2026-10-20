-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_gammaDivergenceComparison
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.gammaDivergenceComparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:54:31.759449+00:00
-- url     : https://prove2.me/theorems/b6c12759-e223-4cd9-bf46-336ef9f80423
-- title:
--   Comparison of Gamma with C_gamma
-- statement:
--   All systems are finite-dimensional and nonzero, with fixed orthonormal product bases, and logarithms are base two. States are positive semidefinite matrices of trace one. For a positive bipartite operator $s$, define $\gamma(s)$ as the infimum of $\operatorname{Tr}(K_A\otimes L_B)$ over Hermitian $K_A,L_B,V_{AB}$ satisfying $T_B(V_{AB}\pm s)\ge0$ and $K_A\otimes L_B\pm V_{AB}\ge0$, with both signs required. Here $T_B$ transposes only Bob's system. Set $C_\gamma(s)=\log_2\gamma(s)$, with $\log_2 0=-\infty$.
--
--   Let $D$ be a dimension-compatible extended-real generalized divergence satisfying data processing for every CPTP channel, $D(r\|cs)=D(r\|s)-\log_2c$ for $c>0$, and $D(r\|r)=0$. Comparisons need not be normalized and divergence values are not truncated to be nonnegative. Write
--   $$\Gamma_D(r)=\inf_{s\ge0:\,\gamma(s)\le1}D(r\|s).$$
--
--   For every bipartite state $r$,
--   $$\Gamma_D(r)\le D\!\left(r\middle\|\frac{r}{\gamma(r)}\right)=C_\gamma(r).$$
--
--   The comparison is computed from $r$; the finiteness and positivity of $\gamma(r)$ are not assumptions. This relates the divergence measure to the direct trace optimization.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 2, III, comparison (5)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Section III, PDF p.2, (5): comparison and equality with its constructed operator. -/
theorem gammaDivergenceComparison (D : Divergence) (hD : IsGeneralizedDivergence D)
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho) :
    capitalGamma D rho ≤ D rho (normalizedComparison rho) ∧
      D rho (normalizedComparison rho) = cGamma rho := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
