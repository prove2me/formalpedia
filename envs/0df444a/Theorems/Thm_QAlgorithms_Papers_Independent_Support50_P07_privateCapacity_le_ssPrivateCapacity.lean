-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_privateCapacity_le_ssPrivateCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P07.privateCapacity_le_ssPrivateCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:50:32.922932+00:00
-- url     : https://prove2.me/theorems/3c5e1c0a-9b87-42b3-8649-a4e3c08144db
-- title:
--   Unnumbered result used in Theorem 11: unassisted capacity is bounded by ss-private capacity
-- statement:
--   For every channel $\mathcal N$, unassisted private communication is bounded by free symmetric-side-channel-assisted private communication:
--
--   $$C_p(\mathcal N)\le C_{p,ss}(\mathcal N).$$
--
--   Both capacities use uniform messages and joint full-trace-norm correctness and security against the full environment.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 5, Unnumbered result used in Theorem 11: unassisted capacity is bounded by ss-private capacity

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

/-- PDF pp.1,5: ignoring the d=1 side channel recovers every unassisted code. -/
theorem privateCapacity_le_ssPrivateCapacity [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ)
    (hU : IsIsometry U) :
    fullTracePrivateCapacity U ≤ ssPrivateCapacity U := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
