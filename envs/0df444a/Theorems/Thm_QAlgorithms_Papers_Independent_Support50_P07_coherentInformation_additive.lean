-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_coherentInformation_additive
-- name    : QAlgorithms.Papers.Independent.Support50.P07.coherentInformation_additive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:42:40.304091+00:00
-- url     : https://prove2.me/theorems/572034b0-4a84-47b7-9957-ab4e9b9abe55
-- title:
--   Lemma 4: additivity of maximum coherent information for degradable channels
-- statement:
--   Let $\mathcal N_1$ and $\mathcal N_2$ be any two degradable channels, with independently fixed Stinespring isometries. For each channel write $Q^{(1)}$ for the supremum of $S(B)-S(E)$ over all normalized input density operators. Then
--
--   $$Q^{(1)}(\mathcal N_1\otimes\mathcal N_2)=Q^{(1)}(\mathcal N_1)+Q^{(1)}(\mathcal N_2).$$
--
--   The product optimization allows entangled inputs.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 3, Lemma 4: additivity of maximum coherent information for degradable channels

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

/-- Lemma 4, PDF p.3, prior result [9] with an alternate proof here: additivity for
TWO arbitrary degradable channels, without restricting the joint input to product states. -/
theorem coherentInformation_additive [Nonempty A] [Nonempty B] [Nonempty E]
    [Nonempty C] [Nonempty D] [Nonempty F]
    (U : Matrix (B × E) A ℂ)
    (V : Matrix (D × F) C ℂ) (hU : IsIsometry U) (hV : IsIsometry V)
    (hdU : IsDegradable U) (hdV : IsDegradable V) :
    maximumCoherentInformation (productDilation U V) =
      maximumCoherentInformation U + maximumCoherentInformation V := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
