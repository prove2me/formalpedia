-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_multiwayRegionProperties
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.multiwayRegionProperties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:13:32.03211+00:00
-- url     : https://prove2.me/theorems/025d9709-4339-4d02-acda-b18239cd9dc6
-- title:
--   III-capacity-region-properties: Operational multiway capacity region is closed and convex.
-- statement:
--   Fix a finite classical-input quantum multiway channel with separate deterministic encoders, independent uniform messages and commuting intrinsic receiver accesses. Achievability requires actual codes at every sufficiently large length for each positive rate slack and error tolerance; the error is wrong entire tuple at each receiver.
--
--   $$
--   \mathcal C(W)\text{ is closed and convex}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 41, III-capacity-region-properties

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Unnumbered capacity-region properties, PDF p.41. The imported model has fixed
finite classical alphabets and commuting intrinsic receiver accesses. -/
theorem multiwayRegionProperties {s r : ℕ}
    {C : QAlgorithms.Papers.Independent.Claimed50.P40.ClassicalChannel s}
    (N : QAlgorithms.Papers.Independent.Claimed50.P40.Network C r) :
    IsClosed (QAlgorithms.Papers.Independent.Claimed50.P40.capacityRegion N) ∧
    Convex ℝ (QAlgorithms.Papers.Independent.Claimed50.P40.capacityRegion N) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
