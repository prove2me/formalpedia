-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_operational_ordering
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.operational_ordering
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:49:34.262848+00:00
-- url     : https://prove2.me/theorems/5b6b5377-7def-4f55-80df-d6f28e6018f1
-- title:
--   Eq.(41): operational capacity/simulation-cost ordering
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   For a CPTP channel $\mathcal N$, write $Q_E,Q_{\rm NS}$ for operational quantum capacities with entanglement and NS assistance, and $S_E,S_{\rm NS}$ for the corresponding operational simulation costs. All are vanishing-error rates of noiseless quantum dimensions. Then
--
--   $$Q_E(\mathcal N)\le Q_{\rm NS}(\mathcal N)\le S_{\rm NS}(\mathcal N)\le S_E(\mathcal N).$$
--
--   The four quantities are independently defined using communication or simulation codes, and entanglement assistance is implemented by local maps and a shared density matrix.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 10, Eq.(41): operational capacity/simulation-cost ordering

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P65

noncomputable section

open Filter QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakethird100.P65

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (transposeBob)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Independent2.P01 (dampingKraus damping)

open QAlgorithms.Papers.Independent.Gap48.P33 (phaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P62 (Stochastic)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized purifiedDistance)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer permute)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond channelPower channelRelative)

open QAlgorithms.Papers.Independent.Support50.P39 (quantumMutualInformation)

variable {A B C D R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty R]

/-- Eq.(41), PDF p.10: all four operational quantities and all three inequalities. -/
theorem operational_ordering (N : Superop A B) (hN : IsChannel N) :
    vanishingErrorQuantumCapacity .ent N ≤ vanishingErrorQuantumCapacity .ns N ∧ vanishingErrorQuantumCapacity .ns N ≤ vanishingErrorSimulationCost .ns N ∧
    vanishingErrorSimulationCost .ns N ≤ vanishingErrorSimulationCost .ent N := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
