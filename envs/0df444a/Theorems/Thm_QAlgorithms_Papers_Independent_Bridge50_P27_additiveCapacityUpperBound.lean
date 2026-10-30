-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P27_additiveCapacityUpperBound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P27.additiveCapacityUpperBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:24:52.650978+00:00
-- url     : https://prove2.me/theorems/bf5cb8e0-3255-4c28-9f26-c9ea997d8d4a
-- title:
--   Operational mean-constrained additive capacity upper bound
-- statement:
--   Fix $v,N_S\ge0$. Let $C(\mathcal N_v,N_S)$ be the unassisted classical capacity defined as the extended nonnegative supremum of achievable rates: for every positive error tolerance and rate slack, all sufficiently large positive blocklengths admit normalized block codes, arbitrary collective POVMs, rate at least the target minus the slack, vanishing average error, and total mean photons at most $nN_S$ for each message. Then
--
--   $$C(\mathcal N_v,N_S)\le g\!\left(\frac{N_S}{v+1}\right).$$
--
--   This is the apparently new weak capacity upper bound (13). Its energy hypothesis is a mean constraint, without the maximum occupation requirement of the strong converse in Section 5.2. The zero-noise identity channel is included.
-- source:
--   Strong converse rates for classical communication over thermal and additive noise bosonic channels, arXiv:1312.3287v2, PDF p. 5, §3.2, (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P27

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

-- Exact accepted definitions, checked against their complete source bodies.

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits)

open QAlgorithms.Papers.Independent.Renew46.P30 (photonTotal)

open QAlgorithms.Papers.Independent.Support50.P06 (totalEnergy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section 3.2, PDF p.5, (13), and decomposition (16), PDF p.6.
The mean-energy operational capacity is bounded; no maximum-occupation constraint
is imposed. This is distinct from Section 5.2's strong converse rate. -/
theorem additiveCapacityUpperBound (v NS : ℝ) (hv : 0 ≤ v) (hNS : 0 ≤ NS) :
    meanEnergyClassicalCapacity (.additive v) NS ≤ ENNReal.ofReal (bosonicEntropy (NS / (v + 1))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P27

end
