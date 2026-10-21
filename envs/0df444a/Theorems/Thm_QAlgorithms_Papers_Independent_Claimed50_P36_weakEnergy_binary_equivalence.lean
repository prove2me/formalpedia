-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P36_weakEnergy_binary_equivalence
-- name    : QAlgorithms.Papers.Independent.Claimed50.P36.weakEnergy_binary_equivalence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:35:51.285257+00:00
-- url     : https://prove2.me/theorems/2a1d44ac-9529-492d-b1c4-dbfca4dbfa69
-- title:
--   Weak-energy continuous and binary capacity expansions
-- statement:
--   Let $C_{\rm BE}(m)$ be the noiseless continuous coherent capacity and $C^{(2)}(m)$ its optimal binary collective discretization, with transmitted photon budget $m$ and rates in nats per mode. As $m$ tends to zero through positive reals,
--
--   $$
--   C_{\rm BE}(m)=-m\log m+m+o(m),\qquad C^{(2)}(m)=-m\log m+m+o(m).
--   $$
--
--   Each remainder divided by $m$ tends to zero. This formalizes the two terms specified by the source without imposing a finite-budget approximation tolerance. The capacities allow collective decoding and are distinct from binary single-symbol accessible information.
-- source:
--   Information capacity formula of quantum optical channels, arXiv:quant-ph/0105042v1, PDF p. 17, Eq.(71)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P36

open Filter

open scoped Topology ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable

-- Reuse the pinned accepted entropy definitions, preserving their codomains
-- and units. P24.bosonicEntropy is in bits: multiply by log 2 for nats.
-- P01.binaryEntropy is in nats and ENNReal-valued: use toReal only at the
-- finite binary-probability argument of binaryValue below.

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

/-- PDF p.17, Eq.(71): the two specified terms of the weak-energy expansion,
with error o(m). The limit is through positive real photon budgets. -/
theorem weakEnergy_binary_equivalence :
    Tendsto (fun m : ℝ =>
      (coherentCapacity m - (-m * Real.log m + m)) / m)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
    Tendsto (fun m : ℝ =>
      (binaryCollectiveCapacity m - (-m * Real.log m + m)) / m)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P36

end
