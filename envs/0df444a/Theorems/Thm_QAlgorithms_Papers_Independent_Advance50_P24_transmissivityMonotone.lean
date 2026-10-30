-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P24_transmissivityMonotone
-- name    : QAlgorithms.Papers.Independent.Advance50.P24.transmissivityMonotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:57:52.980797+00:00
-- url     : https://prove2.me/theorems/0bf2a8b8-c697-4fa4-85e6-9173ed0b2158
-- title:
--   Capacity increases with transmissivity
-- statement:
--   Let $N>0$ and $0\le\eta_2\le\eta_1\le1$. For the full-Fock vacuum-loss private capacities in nats with the same codebook-average photon budget, arbitrary mixed block inputs and collective normalized decoding,
--
--   $$C_P(\eta_2,N)\le C_P(\eta_1,N).$$
--
--   Thus improving Bob's transmissivity cannot reduce private capacity. The channel degradation is a conclusion of the physical loss model, not a hypothesis.
-- source:
--   Private-Capacity Bounds for Bosonic Wiretap Channels, arXiv:1202.1126v1, PDF p. 2, Lemma 1, (10): monotonicity in transmissivity

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P24

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology ComplexOrder Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Support50.P06
  (BosonicPrivateCode randomizedPrivateCodePhotonBudget
   holevoMessagePrivacyCapacityNats)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel beamCoefficient vacuum bobMarginal charlieMarginal
   spectralEntropyNats realFockTracePair)

open QAlgorithms.Papers.Independent.Dependency50.P16 (majorizedBy)

open QAlgorithms.Papers.Independent.Renew46.P30 (passiveEntry)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

open QAlgorithms.Papers.Independent.Next46.P32 (FockPOVM)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 1, PDF p.2, (10): monotonicity with the printed strict N>0.
No degrading map is assumed, including at eta1=eta2=0. -/
theorem transmissivityMonotone (eta1 eta2 N : ℝ)
    (hzero : 0 ≤ eta2) (horder : eta2 ≤ eta1) (hone : eta1 ≤ 1) (hN : 0 < N) :
    singleCapacity eta2 N ≤ singleCapacity eta1 N := by sorry

end QAlgorithms.Papers.Independent.Advance50.P24

end
