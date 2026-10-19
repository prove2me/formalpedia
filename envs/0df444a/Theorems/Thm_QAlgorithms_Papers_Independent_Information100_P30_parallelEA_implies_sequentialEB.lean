-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P30_parallelEA_implies_sequentialEB
-- name    : QAlgorithms.Papers.Independent.Information100.P30.parallelEA_implies_sequentialEB
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:19:05.609105+00:00
-- url     : https://prove2.me/theorems/9e7387e2-8472-412c-a3fa-c5446e8fc032
-- title:
--   Parallel EA implies sequential EB
-- statement:
--   Let $\Lambda_1,\Lambda_2$ be arbitrary complex-linear completely positive trace-preserving maps on qubit matrices. Suppose the parallel action sends every positive semidefinite bipartite operator to a finite sum of positive product operators. Then
--
--   $$\Lambda_2\circ\Lambda_1\in\mathrm{EB}.$$
--
--   Here EB means that applying the channel to one subsystem of any density operator, with any finite-dimensional reference, gives a separable density operator. This establishes qualitative endpoint-to-midpoint feasibility without a strict-positivity or Kraus-rank restriction.
-- source:
--   Feasibility Ordering of Entanglement-Source Placement for Qubit Channels, arXiv:2609.18803v1, PDF p. 4, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P30

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Theorem 1 (PDF p.4, Eqs.(37)–(38); abstract p.1): arbitrary qubit channels,
including boundary channels, satisfy parallel EA implies ordered sequential EB. -/
theorem parallelEA_implies_sequentialEB (F G : MatrixMap Bool Bool)
    (hF : IsQubitChannel F) (hG : IsQubitChannel G) (hEA : IsParallelEA F G) :
    Entanglement.IsEntanglementBreaking (G.comp F) := by sorry

end QAlgorithms.Papers.Independent.Information100.P30

end
