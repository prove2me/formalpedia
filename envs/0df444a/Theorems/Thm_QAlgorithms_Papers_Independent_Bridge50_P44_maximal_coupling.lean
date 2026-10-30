-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_maximal_coupling
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.maximal_coupling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:13:09.574039+00:00
-- url     : https://prove2.me/theorems/7a742451-728f-4f03-b9e0-9eb7eaf8dcc3
-- title:
--   Theorem A.6: maximal coupling
-- statement:
--   Let $P,Q$ be normalized discrete laws on the same alphabet $Z$. There exists a nonnegative, summable joint law $J$ on $Z\times Z$ with total mass one such that
--
--   $$\sum_w J(z,w)=P(z),\qquad \sum_z J(z,w)=Q(w),\qquad \sum_z J(z,z)\ge1-D(P,Q).$$
--
--   Both marginal equations hold for every respective argument. This maximal coupling result, attributed to Thorisson [Tho00], includes $P=Q$ and does not require positive total variation.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 40, Theorem A.6: maximal coupling

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

/-- PDF pp.40--42, Theorem A.6 (Thorisson): maximal coupling, including equal laws.
Both marginals and normalization of the joint law are part of IsCoupling. -/
theorem maximal_coupling {Z : Type*} (p q : Z → ℝ)
    (hp : IsDiscreteLaw p) (hq : IsDiscreteLaw q) :
    ∃ j : Z × Z → ℝ, IsCoupling p q j ∧
      1 - discreteTV p q ≤ ∑' z, j (z,z) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
