-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P18_positiveHomogeneity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P18.positiveHomogeneity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:59:17.313613+00:00
-- url     : https://prove2.me/theorems/5e7c2c0a-e6c1-4ddd-89cb-ae90095b9265
-- title:
--   Positive homogeneity of gamma
-- statement:
--   All systems are finite-dimensional and nonzero, with fixed orthonormal product bases, and logarithms are base two. States are positive semidefinite matrices of trace one. For a positive bipartite operator $s$, define $\gamma(s)$ as the infimum of $\operatorname{Tr}(K_A\otimes L_B)$ over Hermitian $K_A,L_B,V_{AB}$ satisfying $T_B(V_{AB}\pm s)\ge0$ and $K_A\otimes L_B\pm V_{AB}\ge0$, with both signs required. Here $T_B$ transposes only Bob's system. Set $C_\gamma(s)=\log_2\gamma(s)$, with $\log_2 0=-\infty$.
--
--   For every positive operator $s_{AB}$ and every real $c>0$,
--   $$\gamma(cs)=c\gamma(s).$$
--
--   The zero operator is allowed. Although called scale invariance in the source, the equation is positive homogeneity of degree one, which controls normalization of comparison operators.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, PDF p. 3, Proposition 6, (16)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Proposition 6, PDF p.3, (16): degree-one homogeneity, allowing sigma=0. -/
theorem positiveHomogeneity (sigma : Matrix (A × B) (A × B) ℂ)
    (hsigma : sigma.PosSemidef) (c : ℝ) (hc : 0 < c) :
    correlationGauge ((c : ℂ) • sigma) = (c : EReal) * correlationGauge sigma := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P18

end
