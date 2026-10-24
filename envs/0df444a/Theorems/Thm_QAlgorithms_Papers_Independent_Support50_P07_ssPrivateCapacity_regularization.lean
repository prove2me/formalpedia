-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_ssPrivateCapacity_regularization
-- name    : QAlgorithms.Papers.Independent.Support50.P07.ssPrivateCapacity_regularization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:43:38.026437+00:00
-- url     : https://prove2.me/theorems/2a84d734-ca6a-46e9-8953-bc96af6158c0
-- title:
--   Lemma 6: regularized ss-private capacity
-- statement:
--   For any channel $\mathcal N$, let $C_{p,ss}^{(1)}$ denote the symmetric-pure-ensemble variational quantity of Eq.(3), optimizing all finite auxiliary dimensions and classical processings. The sequence of normalized block quantities converges, and
--
--   $$\lim_{n\to\infty}\frac{1}{n}C_{p,ss}^{(1)}(\mathcal N^{\otimes n})=C_{p,ss}(\mathcal N).$$
--
--   Here $n$ counts only memoryless uses of the main channel.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 3, Lemma 6: regularized ss-private capacity

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

/-- Lemma 6, PDF pp.3–4: convergence itself, to the operational capacity, is asserted.
The harmless n=0 value from real division does not enter the tail atTop. -/
theorem ssPrivateCapacity_regularization [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U) :
    Tendsto (fun n : ℕ => ssPrivateInformation (dilationPower U n) / (n : ℝ))
      atTop (nhds (ssPrivateCapacity U)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
