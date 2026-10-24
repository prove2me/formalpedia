-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_degradable_privateCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P07.degradable_privateCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:40:47.432002+00:00
-- url     : https://prove2.me/theorems/b0463b8a-dc6b-4d97-a443-57a1b5a19d73
-- title:
--   Theorem 2: private capacity of a degradable channel
-- statement:
--   Suppose $\mathcal N$ is degradable: there exists a CPTP map from its receiver output to the full complementary output of the same dilation. Let $Q^{(1)}(\mathcal N)=\sup_\rho[S(\mathcal N(\rho))-S(\widehat{\mathcal N}(\rho))]$, optimizing over all density operators on the input. Then
--
--   $$C_p(\mathcal N)=Q(\mathcal N)=Q^{(1)}(\mathcal N)=\sup_{|\phi\rangle_{RA}} I(R\rangle B)_{(\mathrm{id}_R\otimes\mathcal N)(|\phi\rangle\langle\phi|)}.$$
--
--   Here $I(R\rangle B)=S(B)-S(RB)$, the vectors $\phi$ are normalized purifications, and a reference copy $R\simeq A$ suffices.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 2, Theorem 2: private capacity of a degradable channel

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

/-- Theorem 2, PDF pp.2–3: the unrestricted mixed-input coherent-information optimum,
equivalently the pure-reference/input purification optimum, equals private capacity.
The operational equality Cp=Q announced immediately before the theorem is retained. -/
theorem degradable_privateCapacity [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ)
    (hU : IsIsometry U) (hd : IsDegradable U) :
    fullTracePrivateCapacity U = maximumCoherentInformation U ∧
    maximumCoherentInformation U = purificationCoherentInformation U ∧
    fullTracePrivateCapacity U =
      QAlgorithms.Papers.Independent.Information100.P80.quantumCapacity (receiverChannel U) := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
