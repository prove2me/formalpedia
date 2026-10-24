-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_privateCapacity_le_degradableMixingCost
-- name    : QAlgorithms.Papers.Independent.Support50.P07.privateCapacity_le_degradableMixingCost
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:47:23.276195+00:00
-- url     : https://prove2.me/theorems/303b9e44-aa24-447c-a1f5-d3ee6e9be94b
-- title:
--   Theorem 11: cost of degradable mixing bounds private capacity
-- statement:
--   For a channel $\mathcal N:A\to B$, consider every finite decomposition $\mathcal N=\sum_i p_i\mathcal D_i\circ\mathcal N_i$, where $p_i\ge0$, $\sum_i p_i=1$, each $\mathcal N_i$ is degradable or antidegradable, and each $\mathcal D_i$ is CPTP. Branches may have different finite intermediate output and environment dimensions. Define $C_{DM}(\mathcal N)=\inf\sum_i p_iQ^{(1)}(\mathcal N_i)$ over these decompositions. Then
--
--   $$C_p(\mathcal N)\le C_{DM}(\mathcal N).$$
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   The result turns degradable decompositions into general private-capacity upper bounds.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 5, Theorem 11: cost of degradable mixing bounds private capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P07

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Support50.P07

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
    dilationPower idealJoint maximumCoherentInformation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation)

variable {A B E C D F : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]

variable [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]

/-- Theorem 11, PDF p.5: private capacity is bounded by the full cost of degradable
mixing, with the postprocessors of Definition 10 retained. -/
theorem privateCapacity_le_degradableMixingCost [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ)
    (hU : IsIsometry U) :
    fullTracePrivateCapacity U ≤ degradableMixingCost U := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
