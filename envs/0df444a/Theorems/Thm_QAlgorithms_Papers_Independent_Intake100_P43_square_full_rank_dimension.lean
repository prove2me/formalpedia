-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P43_square_full_rank_dimension
-- name    : QAlgorithms.Papers.Independent.Intake100.P43.square_full_rank_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:25:53.408289+00:00
-- url     : https://prove2.me/theorems/388ced6a-7dd9-4774-9c25-da0242855ff0
-- title:
--   Square full-rank subspaces have maximum dimension one
-- statement:
--   Let $d\ge1$ be an integer and let $H=\mathbb C^d\otimes\mathbb C^d$. Among complex linear subspaces in which every nonzero vector has Schmidt rank $d$, a one-dimensional subspace exists, and every such subspace $S$ satisfies
--
--   $$\dim_{\mathbb C}S\le1.$$
--
--   Consequently the exact maximum is one, also for $d=1$. This supplies the full-rank obstruction underlying the maximally entangled subspace application.
-- source:
--   On the dimension of subspaces with bounded Schmidt rank, arXiv:0706.0705v1, PDF p. 1, Introduction, square full-rank case

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

/-- PDF p.1, unnumbered square full-rank result: the maximum is one.
The determinant paragraph's r in this regime is read as d. The bound applies
without imposing maximal-entanglement entropy or unit norm. -/
theorem square_full_rank_dimension (d : ℕ) (hd : 0 < d) :
    (∃ S : Submodule ℂ (Bipartite d d),
      HasLowerSchmidtRank S d ∧ Module.finrank ℂ S = 1) ∧
    (∀ S : Submodule ℂ (Bipartite d d), HasLowerSchmidtRank S d →
      Module.finrank ℂ S ≤ 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P43

end
