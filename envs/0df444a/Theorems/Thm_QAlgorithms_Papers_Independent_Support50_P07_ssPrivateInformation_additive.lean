-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_ssPrivateInformation_additive
-- name    : QAlgorithms.Papers.Independent.Support50.P07.ssPrivateInformation_additive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:44:39.156473+00:00
-- url     : https://prove2.me/theorems/104a6080-50e9-418d-823e-f2aebd92527f
-- title:
--   Lemma 7: additivity of one-letter ss-private information
-- statement:
--   Let $\mathcal N_1,\mathcal N_2$ be arbitrary quantum channels. Define $C_{p,ss}^{(1)}$ by optimizing $I(T;BF)-I(T;EG)$ over all finite symmetric pure input ensembles and finite classical processings. Then
--
--   $$C_{p,ss}^{(1)}(\mathcal N_1\otimes\mathcal N_2)=C_{p,ss}^{(1)}(\mathcal N_1)+C_{p,ss}^{(1)}(\mathcal N_2).$$
--
--   No degradability or equality of receiver and environment dimensions is assumed.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 4, Lemma 7: additivity of one-letter ss-private information

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

/-- Lemma 7, PDF p.4: one-letter ss information is additive for arbitrary channels. -/
theorem ssPrivateInformation_additive [Nonempty A] [Nonempty B] [Nonempty E]
    [Nonempty C] [Nonempty D] [Nonempty F]
    (U : Matrix (B × E) A ℂ)
    (V : Matrix (D × F) C ℂ) (hU : IsIsometry U) (hV : IsIsometry V) :
    ssPrivateInformation (productDilation U V) =
      ssPrivateInformation U + ssPrivateInformation V := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
