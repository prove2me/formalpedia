-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_ssPrivateInformation_symmetricChannels
-- name    : QAlgorithms.Papers.Independent.Support50.P07.ssPrivateInformation_symmetricChannels
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:49:04.898271+00:00
-- url     : https://prove2.me/theorems/7b8f775a-d707-44d5-ab7b-15f065cf07f9
-- title:
--   Equation (4): variational characterization using symmetric channels
-- statement:
--   For each positive integer $d$, let $V_d$ map an orthonormal basis of a $d(d+1)/2$-dimensional input onto the symmetric subspace of $\mathbb C^d\otimes\mathbb C^d$, and set $\mathcal A_d(\rho)=\operatorname{Tr}_G(V_d\rho V_d^\dagger)$. For every channel $\mathcal N$,
--
--   $$C_{p,ss}^{(1)}(\mathcal N)=\sup_{d\ge1} C_p^{(1)}(\mathcal N\otimes\mathcal A_d).$$
--
--   Both one-use quantities optimize finite normalized pure ensembles and classical processing; the left one uses symmetric auxiliary signals.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 3, Equation (4): variational characterization using symmetric channels

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

/-- Equation (4), PDF p.3: unrestricted positive symmetric-channel dimension;
this is the variational equivalence, independent of operational Theorem 5. -/
theorem ssPrivateInformation_symmetricChannels [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ)
    (hU : IsIsometry U) :
    ssPrivateInformation U = sSup {r | ∃ d : ℕ, 0 < d ∧
      r = processedPrivateInformation (productDilation U (symmetricSubspaceEmbedding d))} := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
