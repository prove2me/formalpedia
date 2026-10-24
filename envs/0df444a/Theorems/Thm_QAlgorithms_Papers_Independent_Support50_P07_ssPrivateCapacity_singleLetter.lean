-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_ssPrivateCapacity_singleLetter
-- name    : QAlgorithms.Papers.Independent.Support50.P07.ssPrivateCapacity_singleLetter
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:40:04.606066+00:00
-- url     : https://prove2.me/theorems/011d04a2-5d7b-4256-a50d-6a82a0172f1f
-- title:
--   Theorem 5 (seed paper result): single-letter ss-private capacity
-- statement:
--   For every channel $\mathcal N:A\to B$, let $U:A\to B\otimes E$ be a Stinespring isometry. For every positive integer $d$, let $F$ and $G$ both have dimension $d$. For a finite pure-state ensemble $\{p_x,|\varphi_x\rangle_{AFG}\}$ whose vectors are individually fixed by swapping $F,G$, and any finite classical stochastic processing $X\to T$, evaluate mutual information after applying $U$ on $A$. Then
--
--   $$C_{p,ss}(\mathcal N)=C_{p,ss}^{(1)}(\mathcal N)=\sup_{d,\{p_x,\varphi_x\},X\to T}\bigl[I(T;BF)-I(T;EG)\bigr].$$
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This identifies the operational resource-assisted capacity with a single-use information optimization.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 3, Theorem 5 (seed paper result): single-letter ss-private capacity

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

/-- Theorem 5, PDF pp.3–4: operational equality with the full symmetric-ensemble
formula (3). The printed theorem has superscript (1); its proof identifies the operational capacity. -/
theorem ssPrivateCapacity_singleLetter [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U) :
    ssPrivateCapacity U = ssPrivateInformation U := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
