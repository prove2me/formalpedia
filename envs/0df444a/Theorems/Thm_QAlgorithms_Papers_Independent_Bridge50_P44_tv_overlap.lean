-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_tv_overlap
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.tv_overlap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:08:33.976998+00:00
-- url     : https://prove2.me/theorems/e37f85f6-bd41-488e-bbe0-b208d5fa3d33
-- title:
--   A.1 Eq.(18): total variation as overlap deficit
-- statement:
--   Let $P$ and $Q$ be normalized discrete probability laws on the same alphabet $Z$. Their nonnegative mass functions have absolutely convergent sums equal to one. With $D(P,Q)=\frac12\sum_z|P(z)-Q(z)|$,
--
--   $$D(P,Q)=1-\sum_{z\in Z}\min\{P(z),Q(z)\}.$$
--
--   This identity expresses total variation as the deficit of common probability mass and applies to finite or countably supported laws.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 36, A.1 Eq.(18): total variation as overlap deficit

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

/-- PDF p.36, Eq.(18): total variation is the deficit of overlap mass. -/
theorem tv_overlap {Z : Type*} (p q : Z → ℝ)
    (hp : IsDiscreteLaw p) (hq : IsDiscreteLaw q) :
    discreteTV p q = 1 - ∑' z, min (p z) (q z) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
