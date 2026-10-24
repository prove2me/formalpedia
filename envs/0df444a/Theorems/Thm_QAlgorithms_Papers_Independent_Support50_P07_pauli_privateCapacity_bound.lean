-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_pauli_privateCapacity_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P07.pauli_privateCapacity_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:48:22.045766+00:00
-- url     : https://prove2.me/theorems/5e09cc63-56b2-4cd1-9f2b-1958a0afd7b0
-- title:
--   Theorem 12: entropy upper bound for a general Pauli channel
-- statement:
--   Let $p_1,p_2,p_3\ge0$ have sum $s=p_1+p_2+p_3\le1$, and let $X,Y,Z$ be the standard qubit Pauli matrices. For the channel $\mathcal N_{\mathbf p}(\rho)=(1-s)\rho+p_1X\rho X+p_2Y\rho Y+p_3Z\rho Z$, with any full Stinespring realization, one has
--
--   $$C_p(\mathcal N_{\mathbf p})\le1-H(s).$$
--
--   The identity endpoint $s=0$ is included; $H$ is binary entropy in bits.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 7, Theorem 12: entropy upper bound for a general Pauli channel

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

/-- Theorem 12, PDF p.7: full probability simplex, including the identity endpoint.
The proof's p_i/s at s=0 is not a hypothesis of this statement. -/
theorem pauli_privateCapacity_bound [Nonempty E]
    (U : Matrix (Fin 2 × E) (Fin 2) ℂ)
    (hU : IsIsometry U) (p : Fin 3 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i ≤ 1) (hmap : receiverChannel U = qubitPauliProbabilityChannel p) :
    fullTracePrivateCapacity U ≤ 1 - binEntropy2 (∑ i, p i) := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
