-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P43_antisymmetric_three_dimension_rank
-- name    : QAlgorithms.Papers.Independent.Intake100.P43.antisymmetric_three_dimension_rank
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:32:17.434395+00:00
-- url     : https://prove2.me/theorems/f1580a95-9f8e-46cb-a38f-08620ac73ac3
-- title:
--   The three-dimensional antisymmetric subspace has rank two
-- statement:
--   In $\mathbb C^3\otimes\mathbb C^3$, let $S$ be the completely antisymmetric subspace: its coefficient matrices obey $M^{\mathsf T}=-M$, with ordinary transpose. Then
--
--   $$\dim_{\mathbb C}S=3,\qquad \operatorname{Sch}(v)=2\quad(0\ne v\in S).$$
--
--   This is a named constant-rank example distinct from the rectangular full-rank construction.
-- source:
--   On the dimension of subspaces with bounded Schmidt rank, arXiv:0706.0705v1, PDF p. 3, Unnumbered antisymmetric example

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

/-- PDF p.3, unnumbered antisymmetric example: the named subspace of
C^3 tensor C^3 has complex dimension three and constant nonzero rank two. -/
theorem antisymmetric_three_dimension_rank :
    Module.finrank ℂ antisymmetricSubspace = 3 ∧
      HasConstantSchmidtRank antisymmetricSubspace 2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P43

end
