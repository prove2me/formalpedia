-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_degradable_privateInformation
-- name    : QAlgorithms.Papers.Independent.Support50.P07.degradable_privateInformation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:41:28.084333+00:00
-- url     : https://prove2.me/theorems/c4401ee4-cd1e-40d6-b6c6-855f0d408a03
-- title:
--   Lemma 3: noisy processing does not improve the private information of a degradable channel
-- statement:
--   For a degradable channel $\mathcal N$, optimize $C_p^{(1)}$ over all finite normalized pure signal ensembles and all finite stochastic processings $X\to T$, with the same dilation defining receiver $B$ and environment $E$. Then
--
--   $$C_p^{(1)}(\mathcal N):=\sup_{\{p_x,\varphi_x\},X\to T}[I(T;B)-I(T;E)]=Q^{(1)}(\mathcal N)=\sup_{\phi_{RA}}I(R\rangle B).$$
--
--   The last supremum is over normalized purifications with reference isomorphic to the input; $Q^{(1)}$ optimizes $S(B)-S(E)$ over arbitrary input density operators.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 2, Lemma 3: noisy processing does not improve the private information of a degradable channel

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

/-- Lemma 3, PDF p.2: classical noisy processing gives no one-use advantage for degradable N. -/
theorem degradable_privateInformation [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ)
    (hU : IsIsometry U) (hd : IsDegradable U) :
    processedPrivateInformation U = maximumCoherentInformation U ∧
    maximumCoherentInformation U = purificationCoherentInformation U := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
