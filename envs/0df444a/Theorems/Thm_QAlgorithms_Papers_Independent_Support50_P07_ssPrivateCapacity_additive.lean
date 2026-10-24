-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_ssPrivateCapacity_additive
-- name    : QAlgorithms.Papers.Independent.Support50.P07.ssPrivateCapacity_additive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:49:42.647043+00:00
-- url     : https://prove2.me/theorems/ed46b100-e066-41df-8752-a0cd6c49994f
-- title:
--   Unnumbered main result: additivity of operational ss-private capacity
-- statement:
--   For arbitrary channels $\mathcal N_1,\mathcal N_2$, the operational symmetric-side-channel-assisted private capacity obeys
--
--   $$C_{p,ss}(\mathcal N_1\otimes\mathcal N_2)=C_{p,ss}(\mathcal N_1)+C_{p,ss}(\mathcal N_2).$$
--
--   Codes may use arbitrary entangled inputs and an arbitrary free finite symmetric side channel in each block.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 1, Unnumbered main result: additivity of operational ss-private capacity

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

/-- Abstract, PDF p.1; derived on p.4: additivity of the OPERATIONAL ss capacity. -/
theorem ssPrivateCapacity_additive [Nonempty A] [Nonempty B] [Nonempty E]
    [Nonempty C] [Nonempty D] [Nonempty F]
    (U : Matrix (B × E) A ℂ)
    (V : Matrix (D × F) C ℂ) (hU : IsIsometry U) (hV : IsIsometry V) :
    ssPrivateCapacity (productDilation U V) =
      ssPrivateCapacity U + ssPrivateCapacity V := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
