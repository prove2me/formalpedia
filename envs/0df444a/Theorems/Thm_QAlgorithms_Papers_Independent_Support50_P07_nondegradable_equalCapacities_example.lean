-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_nondegradable_equalCapacities_example
-- name    : QAlgorithms.Papers.Independent.Support50.P07.nondegradable_equalCapacities_example
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:53:11.587874+00:00
-- url     : https://prove2.me/theorems/1cd351f3-bf4d-4008-a122-7e58dcc8636a
-- title:
--   Unnumbered main example: nondegradable channels with equal private and quantum capacities
-- statement:
--   There exist extremal qubit channels $\mathcal N_1,\mathcal N_2$, each with a two-dimensional environment, such that $\mathcal N_1$ is degradable but not antidegradable and $\mathcal N_2$ is antidegradable but not degradable. Their product is extremal among all CPTP maps on two qubits and is neither degradable nor antidegradable and satisfies
--
--   $$C_{DM}(\mathcal N_1\otimes\mathcal N_2)=Q(\mathcal N_1\otimes\mathcal N_2)=Q^{(1)}(\mathcal N_1),\qquad C_p(\mathcal N_1\otimes\mathcal N_2)=Q(\mathcal N_1\otimes\mathcal N_2).$$
--
--   Here $Q$ is the operational unassisted quantum capacity.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 5, Unnumbered main example: nondegradable channels with equal private and quantum capacities

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

/-- PDF p.5, example acknowledged to Debbie Leung [27]: an actual product of
extremal qubit channels supplies the existential nondegradable example. Extremality
is in the full convex set of CPTP receiver maps, including for their product.
No genericity measure is invented. Quantum capacity and mixing cost are identified. -/
theorem nondegradable_equalCapacities_example :
    ∃ U V : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ,
      IsIsometry U ∧ IsIsometry V ∧
      receiverChannel U ∈ Set.extremePoints ℝ
        {N : Superop (Fin 2) (Fin 2) | IsChannel N} ∧
      receiverChannel V ∈ Set.extremePoints ℝ
        {N : Superop (Fin 2) (Fin 2) | IsChannel N} ∧
      receiverChannel (productDilation U V) ∈ Set.extremePoints ℝ
        {N : Superop (Fin 2 × Fin 2) (Fin 2 × Fin 2) | IsChannel N} ∧
      IsDegradable U ∧ ¬ IsAntidegradable U ∧
      IsAntidegradable V ∧ ¬ IsDegradable V ∧
      ¬ IsDegradable (productDilation U V) ∧ ¬ IsAntidegradable (productDilation U V) ∧
      degradableMixingCost (productDilation U V) = maximumCoherentInformation U ∧
      QAlgorithms.Papers.Independent.Information100.P80.quantumCapacity
        (receiverChannel (productDilation U V)) = maximumCoherentInformation U ∧
      fullTracePrivateCapacity (productDilation U V) = QAlgorithms.Papers.Independent.Information100.P80.quantumCapacity
        (receiverChannel (productDilation U V)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
