-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P43_lower_rank_attainment
-- name    : QAlgorithms.Papers.Independent.Intake100.P43.lower_rank_attainment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:29:35.112872+00:00
-- url     : https://prove2.me/theorems/31020499-e525-463a-a71d-1f46001d1c2f
-- title:
--   Proposition 10: attaining construction exists
-- statement:
--   Fix local computational bases of $H=\mathbb C^{d_A}\otimes\mathbb C^{d_B}$, where $1\le d_A\le d_B$, and an integer $1\le r\le d_A$. All subspaces and dimensions are complex. Write $\operatorname{Sch}(v)$ for the rank of the coefficient matrix of $v$. Subspace rank conditions concern every nonzero vector and do not require unit norm. There exists a complex linear subspace $S\subseteq H$ such that every nonzero $v\in S$ has $\operatorname{Sch}(v)\ge r$ and
--
--   $$\dim_{\mathbb C}S=(d_A-r+1)(d_B-r+1).$$
--
--   This attains the universal upper bound. The statement includes the trivial $r=1$ case without turning the proof’s diagonal construction into an extra hypothesis.
-- source:
--   On the dimension of subspaces with bounded Schmidt rank, arXiv:0706.0705v1, PDF p. 3, Proposition 10

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

/-- PDF p.3, Proposition 10: an attaining subspace exists, with no proof-built
diagonal construction or determinantal identity added as a hypothesis. -/
theorem lower_rank_attainment (dA dB r : ℕ)
    (hA : 0 < dA) (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA) :
    ∃ S : Submodule ℂ (Bipartite dA dB), HasLowerSchmidtRank S r ∧
      Module.finrank ℂ S = (dA - r + 1) * (dB - r + 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P43

end
