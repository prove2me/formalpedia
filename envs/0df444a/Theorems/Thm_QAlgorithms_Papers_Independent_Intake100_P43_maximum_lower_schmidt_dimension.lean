-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P43_maximum_lower_schmidt_dimension
-- name    : QAlgorithms.Papers.Independent.Intake100.P43.maximum_lower_schmidt_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:24:49.165649+00:00
-- url     : https://prove2.me/theorems/20f354d8-0897-43ca-96b1-ddb73b856d34
-- title:
--   Theorem 11: exact maximum dimension with Schmidt rank at least r
-- statement:
--   Fix local computational bases of $H=\mathbb C^{d_A}\otimes\mathbb C^{d_B}$, where $1\le d_A\le d_B$, and an integer $1\le r\le d_A$. All subspaces and dimensions are complex. Write $\operatorname{Sch}(v)$ for the rank of the coefficient matrix of $v$. Subspace rank conditions concern every nonzero vector and do not require unit norm. There exists a subspace $S$ all of whose nonzero vectors have Schmidt rank at least $r$ and whose dimension is $N=(d_A-r+1)(d_B-r+1)$. Every subspace $T$ with this rank property satisfies
--
--   $$\dim_{\mathbb C}T\le N=(d_A-r+1)(d_B-r+1).$$
--
--   Thus the bound is attained, including the full-space case $r=1$. This is the paper’s exact dimension optimum.
-- source:
--   On the dimension of subspaces with bounded Schmidt rank, arXiv:0706.0705v1, PDF p. 3, Theorem 11

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

/-- PDF p.3, Theorem 11: exact maximum, including attainment and the universal
upper bound. PDF p.1 explicitly allows the trivial r=1 full-space case. -/
theorem maximum_lower_schmidt_dimension (dA dB r : ℕ)
    (hA : 0 < dA) (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA) :
    (∃ S : Submodule ℂ (Bipartite dA dB),
      HasLowerSchmidtRank S r ∧
      Module.finrank ℂ S = (dA - r + 1) * (dB - r + 1)) ∧
    (∀ S : Submodule ℂ (Bipartite dA dB), HasLowerSchmidtRank S r →
      Module.finrank ℂ S ≤ (dA - r + 1) * (dB - r + 1)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P43

end
