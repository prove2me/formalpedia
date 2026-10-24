-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_ssPrivateCapacity_postprocessing
-- name    : QAlgorithms.Papers.Independent.Support50.P07.ssPrivateCapacity_postprocessing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:51:27.52022+00:00
-- url     : https://prove2.me/theorems/99d0f7c1-3eec-495b-bd09-166cb26d2205
-- title:
--   Unnumbered data-processing result for ss-private capacity
-- statement:
--   Let $\mathcal N:A\to B$ be a channel and let $\mathcal D:B\to C$ be any CPTP receiver postprocessing. Realize the composition by any full Stinespring dilation, whose environment includes the information discarded by postprocessing. Then
--
--   $$C_{p,ss}(\mathcal D\circ\mathcal N)\le C_{p,ss}(\mathcal N).$$
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 5, Unnumbered data-processing result for ss-private capacity

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

/-- PDF p.5: arbitrary receiverChannel CPTP postprocessing, with its environment added to Eve. -/
theorem ssPrivateCapacity_postprocessing [Nonempty A] [Nonempty B] [Nonempty E]
    [Nonempty D] [Nonempty F]
    (U : Matrix (B × E) A ℂ)
    (V : Matrix (D × F) A ℂ) (hU : IsIsometry U) (hV : IsIsometry V)
    (post : Superop B D) (hpost : IsChannel post)
    (hmap : ∀ rho, receiverChannel V rho = post (receiverChannel U rho)) :
    ssPrivateCapacity V ≤ ssPrivateCapacity U := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
