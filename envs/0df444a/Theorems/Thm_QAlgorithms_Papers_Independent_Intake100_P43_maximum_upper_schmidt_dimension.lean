-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P43_maximum_upper_schmidt_dimension
-- name    : QAlgorithms.Papers.Independent.Intake100.P43.maximum_upper_schmidt_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:30:26.937975+00:00
-- url     : https://prove2.me/theorems/8fc396a3-a728-47dd-8bb8-9afad8d09ce5
-- title:
--   Exact maximum dimension with Schmidt rank at most r
-- statement:
--   Fix local computational bases of $H=\mathbb C^{d_A}\otimes\mathbb C^{d_B}$, where $1\le d_A\le d_B$, and an integer $1\le r\le d_A$. All subspaces and dimensions are complex. Write $\operatorname{Sch}(v)$ for the rank of the coefficient matrix of $v$. Subspace rank conditions concern every nonzero vector and do not require unit norm. A subspace of dimension $rd_B$ exists in which every nonzero vector has Schmidt rank at most $r$. Every complex linear subspace $T\subseteq H$ with that rank property satisfies
--
--   $$\dim_{\mathbb C}T\le rd_B.$$
--
--   Thus $rd_B$ is the exact attained maximum. It is achieved by restricting the first tensor factor to an $r$-dimensional subspace.
-- source:
--   On the dimension of subspaces with bounded Schmidt rank, arXiv:0706.0705v1, PDF p. 3, Unnumbered converse preceding Theorem 12

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

/-- PDF p.3, unnumbered converse immediately before Theorem 12: the exact
maximum dimension with Schmidt rank at most r is r*dB, with attainment. -/
theorem maximum_upper_schmidt_dimension (dA dB r : ℕ)
    (hA : 0 < dA) (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA) :
    (∃ S : Submodule ℂ (Bipartite dA dB),
      HasUpperSchmidtRank S r ∧ Module.finrank ℂ S = r * dB) ∧
    (∀ S : Submodule ℂ (Bipartite dA dB), HasUpperSchmidtRank S r →
      Module.finrank ℂ S ≤ r * dB) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P43

end
