-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P43_rectangular_full_rank_subspace
-- name    : QAlgorithms.Papers.Independent.Intake100.P43.rectangular_full_rank_subspace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:31:26.712424+00:00
-- url     : https://prove2.me/theorems/72a1f893-f42a-448c-826d-894f70833edc
-- title:
--   Rectangular subspaces of constant maximum rank
-- statement:
--   For integers $1\le d_A\le d_B$, there exists a complex linear subspace $S\subseteq\mathbb C^{d_A}\otimes\mathbb C^{d_B}$ such that
--
--   $$\dim_{\mathbb C}S=d_B-d_A+1,\qquad \operatorname{Sch}(v)=d_A\quad(0\ne v\in S).$$
--
--   This gives an exact constant-rank example and specializes to dimension one in the square case.
-- source:
--   On the dimension of subspaces with bounded Schmidt rank, arXiv:0706.0705v1, PDF p. 3, Unnumbered constant-rank rectangular example

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

/-- PDF p.3, unnumbered constant-rank rectangular example: exact rank dA
on every nonzero vector, not just a lower rank bound. -/
theorem rectangular_full_rank_subspace (dA dB : ℕ)
    (hA : 0 < dA) (hAB : dA ≤ dB) :
    ∃ S : Submodule ℂ (Bipartite dA dB),
      HasConstantSchmidtRank S dA ∧ Module.finrank ℂ S = dB - dA + 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P43

end
