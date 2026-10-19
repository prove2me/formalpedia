-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P30_strictlyPositive_first_sequentialEB
-- name    : QAlgorithms.Papers.Independent.Information100.P30.strictlyPositive_first_sequentialEB
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:21:55.872823+00:00
-- url     : https://prove2.me/theorems/1a1b9fba-a52a-49cd-8ed2-3d124c368e66
-- title:
--   Strictly positive first channel
-- statement:
--   Let $\Lambda_1,\Lambda_2$ be complex-linear CPTP qubit maps, with $\Lambda_1$ strictly positive: $X\succeq0$ and $X\ne0$ imply $\Lambda_1(X)\succ0$. Then
--
--   $$\Lambda_1\otimes\Lambda_2\in\mathrm{EA}\quad\Longrightarrow\quad\Lambda_2\circ\Lambda_1\in\mathrm{EB}.$$
--
--   EA is defined on the full positive cone and EB on density operators with every finite-dimensional reference. Only the first channel is required to be strictly positive, and factorization is not assumed.
-- source:
--   Feasibility Ordering of Entanglement-Source Placement for Qubit Channels, arXiv:2609.18803v1, PDF p. 3, Corollary 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P30

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Corollary 1 (PDF pp.3–4, Eqs.(31)–(32)): strict positivity is required
only of the first channel in the ordered sequential composition. -/
theorem strictlyPositive_first_sequentialEB (F G : MatrixMap Bool Bool)
    (hF : IsQubitChannel F) (hG : IsQubitChannel G)
    (hstrict : IsStrictlyPositive F) (hEA : IsParallelEA F G) :
    Entanglement.IsEntanglementBreaking (G.comp F) := by sorry

end QAlgorithms.Papers.Independent.Information100.P30

end
