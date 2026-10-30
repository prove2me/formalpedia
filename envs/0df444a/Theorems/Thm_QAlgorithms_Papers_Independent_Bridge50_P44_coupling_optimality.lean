-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_coupling_optimality
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.coupling_optimality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:13:42.235988+00:00
-- url     : https://prove2.me/theorems/3712ec58-eec9-4194-bdaa-9a25695b4965
-- title:
--   A.3: coupling bound is optimal
-- statement:
--   Let $J$ be any normalized discrete joint law with marginals $P$ and $Q$ on a common alphabet. Its agreement probability satisfies
--
--   $$\Pr_J[Z=\widetilde Z]=\sum_zJ(z,z)\le1-D(P,Q).$$
--
--   Together with maximal coupling, this says that the overlap mass is the greatest attainable agreement probability.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 40, A.3: coupling bound is optimal

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P44

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceFirst)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Frontier18.P08 (conditionalEntropyNats)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.40, immediately after Theorem A.6: no coupling can have greater
agreement probability than the overlap mass. -/
theorem coupling_optimality {Z : Type*} (p q : Z → ℝ) (j : Z × Z → ℝ)
    (hj : IsCoupling p q j) :
    (∑' z, j (z,z)) ≤ 1 - discreteTV p q := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
