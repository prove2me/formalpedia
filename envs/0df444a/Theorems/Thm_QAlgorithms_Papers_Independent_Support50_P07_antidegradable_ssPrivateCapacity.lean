-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_antidegradable_ssPrivateCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P07.antidegradable_ssPrivateCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:52:22.957223+00:00
-- url     : https://prove2.me/theorems/d87201ce-85a0-4027-863a-3eb949fe2f41
-- title:
--   Unnumbered result in Theorem 11: antidegradable channels have zero ss-private capacity
-- statement:
--   If $\mathcal N$ is antidegradable, meaning that a CPTP map simulates its receiver from the full complementary output of the same dilation, then
--
--   $$C_{p,ss}(\mathcal N)=Q^{(1)}(\mathcal N)=0.$$
--
--   The one-letter coherent information optimizes over arbitrary normalized input density operators.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
--
--   The conclusion also explicitly includes the unassisted private capacity $C_p(\mathcal N)=0$.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 5, Unnumbered result in Theorem 11: antidegradable channels have zero ss-private capacity

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

/-- PDF pp.5–6: environment-to-receiverChannel simulation forces zero ss-private capacity;
the equality with Q^(1) mentioned in Theorem 11 is retained. -/
theorem antidegradable_ssPrivateCapacity [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ)
    (hU : IsIsometry U) (ha : IsAntidegradable U) :
    ssPrivateCapacity U = 0 ∧ maximumCoherentInformation U = 0 ∧
    fullTracePrivateCapacity U = 0 := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
