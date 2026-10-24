-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_degradable_ssPrivateCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P07.degradable_ssPrivateCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:46:26.182749+00:00
-- url     : https://prove2.me/theorems/77b99410-c8ac-4eda-9e5b-d76f7b00c08c
-- title:
--   Lemma 9: ss assistance does not help degradable channels
-- statement:
--   If $\mathcal N$ is degradable, with its degrading CPTP map simulating the full environment from the receiver, then
--
--   $$C_{p,ss}(\mathcal N)=Q^{(1)}(\mathcal N).$$
--
--   The right side maximizes $S(B)-S(E)$ over all normalized mixed input states.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 5, Lemma 9: ss assistance does not help degradable channels

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

/-- Lemma 9, PDF p.5: free symmetric assistance does not improve degradable channels. -/
theorem degradable_ssPrivateCapacity [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ)
    (hU : IsIsometry U) (hd : IsDegradable U) :
    ssPrivateCapacity U = maximumCoherentInformation U := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
