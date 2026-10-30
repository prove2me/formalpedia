-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P24_singleModeUpperBound
-- name    : QAlgorithms.Papers.Independent.Advance50.P24.singleModeUpperBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:56:49.086164+00:00
-- url     : https://prove2.me/theorems/db34fb63-a8d0-47da-b161-c3a77b134955
-- title:
--   Single-mode unconditional upper bound
-- statement:
--   Let $0\le\eta\le1$ and let $N\ge0$ be a finite mean input photon budget. For the vacuum-loss wiretap channel, let $C_P(\eta,N)$ denote its operational private capacity in nats, with arbitrary mixed block inputs, uniform messages, private randomization, collective normalized decoding POVMs, vanishing message Holevo leakage, and total codebook-average energy at most $nN$ over $n$ uses. Set $g(x)=(1+x)\log(1+x)-x\log x$, continuously extended by $g(0)=0$, and $U(\eta,N)=g((2\eta-1)N)$ for $\eta>1/2$ and zero otherwise. Then
--
--   $$C_P(\eta,N)\le U(\eta,N).$$
--
--   This is unconditional and includes the zero-energy, identity, and antidegradable endpoints.
-- source:
--   Private-Capacity Bounds for Bosonic Wiretap Channels, arXiv:1202.1126v1, PDF p. 2, Theorem 1, (8)–(9): single-mode private-capacity upper bound; original paper seed

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

/-- Theorem 1, PDF p.2, (8)--(9), model on p.1: unconditional upper bound.
In particular this includes N=0 and eta<=1/2; no entropy conjecture is a premise. -/
theorem singleModeUpperBound (eta N : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (hN : 0 ≤ N) :
    singleCapacity eta N ≤ ENNReal.ofReal (upperBound eta N) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P24

end
