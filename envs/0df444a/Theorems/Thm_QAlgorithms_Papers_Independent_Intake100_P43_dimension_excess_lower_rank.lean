-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P43_dimension_excess_lower_rank
-- name    : QAlgorithms.Papers.Independent.Intake100.P43.dimension_excess_lower_rank
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:27:25.1667+00:00
-- url     : https://prove2.me/theorems/cfe29e59-b3f7-430c-b413-2035bda7c62b
-- title:
--   Proposition 6: strict dimension excess forces lower rank
-- statement:
--   Fix local computational bases of $H=\mathbb C^{d_A}\otimes\mathbb C^{d_B}$, where $1\le d_A\le d_B$, and an integer $1\le r\le d_A$. All subspaces and dimensions are complex. Write $\operatorname{Sch}(v)$ for the rank of the coefficient matrix of $v$. Subspace rank conditions concern every nonzero vector and do not require unit norm. If a subspace $S\subseteq H$ satisfies $\dim_{\mathbb C}S>(d_A-r+1)(d_B-r+1)$, then
--
--   $$\exists v\in S\setminus\{0\},\qquad\operatorname{Sch}(v)<r.$$
--
--   This is the dimension upper-bound mechanism. For $r=1$ its dimension premise cannot hold.
-- source:
--   On the dimension of subspaces with bounded Schmidt rank, arXiv:0706.0705v1, PDF p. 2, Proposition 6

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

/-- PDF p.2, Proposition 6: strict dimension excess forces a NONZERO vector
of rank strictly below r. For r=1 the dimension premise is impossible. -/
theorem dimension_excess_lower_rank (dA dB r : ℕ)
    (hA : 0 < dA) (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA)
    (S : Submodule ℂ (Bipartite dA dB))
    (hS : (dA - r + 1) * (dB - r + 1) < Module.finrank ℂ S) :
    ∃ v : Bipartite dA dB, v ∈ S ∧ v ≠ 0 ∧ schmidtNumber v < r := by sorry

end QAlgorithms.Papers.Independent.Intake100.P43

end
