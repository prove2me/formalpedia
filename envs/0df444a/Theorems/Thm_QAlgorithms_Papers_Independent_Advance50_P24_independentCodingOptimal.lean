-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P24_independentCodingOptimal
-- name    : QAlgorithms.Papers.Independent.Advance50.P24.independentCodingOptimal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:00:12.484446+00:00
-- url     : https://prove2.me/theorems/ad54218e-88bf-4fba-b041-02ea62033124
-- title:
--   Independent coding and attained total photon allocation
-- statement:
--   Let $m\ge1$, $\eta\in[0,1]^m$ and $N\ge0$. Let $C_P^M(\eta,N)$ be the operational private capacity in nats of the parallel vacuum-loss channels (25), allowing arbitrary entanglement across modes and uses, with average total block energy at most $nN$. Let $C_P(\eta_i,N_i)$ be the corresponding single-mode capacities. Then an allocation $a_i\ge0$ with $\sum_i a_i=N$ attains
--
--   $$C_P^M(\eta,N)=\max_{a_i\ge0,\ \sum_i a_i=N}\ \sum_{i=1}^m C_P(\eta_i,a_i).$$
--
--   This equality states optimality of independent coding. Attainment and exact total budget are retained even if every mode has zero capacity.
-- source:
--   Private-Capacity Bounds for Bosonic Wiretap Channels, arXiv:1202.1126v1, PDF p. 4, Theorem 4, (34): optimal independent coding and attained photon allocation

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

/-- Theorem 4, PDF p.4, (34): independent coding is optimal, with an attained
allocation of the exact TOTAL budget. This is equality of actual operational
capacities, allowing arbitrary intermode and interuse input entanglement. -/
theorem independentCodingOptimal {m : ℕ} (hm : 0 < m) (eta : Fin m → ℝ)
    (heta : eta ∈ transmissivityCube m) (N : ℝ) (hN : 0 ≤ N) :
    ∃ a ∈ photonBudgetAllocations m N,
      parallelPrivateCapacityNats eta N = ∑ i, singleCapacity (eta i) (a i) ∧
      ∀ b ∈ photonBudgetAllocations m N,
        (∑ i, singleCapacity (eta i) (b i)) ≤ ∑ i, singleCapacity (eta i) (a i) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P24

end
