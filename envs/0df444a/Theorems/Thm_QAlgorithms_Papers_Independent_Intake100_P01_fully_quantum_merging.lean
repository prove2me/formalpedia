-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P01_fully_quantum_merging
-- name    : QAlgorithms.Papers.Independent.Intake100.P01.fully_quantum_merging
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:54:46.858386+00:00
-- url     : https://prove2.me/theorems/cf4c0c94-9130-4243-b2e5-f6faeb67b2e8
-- title:
--   Fully quantum merging (mother protocol), eq.(44), with optimal qubit cost and yield
-- statement:
--   Let $|\psi\rangle_{ABR}$ be a finite-dimensional unit vector. With local CPTP operations, no classical channel, no initial shared Bell resource, and a counted Alice-to-Bob noiseless qubit message, the following pair is asymptotically achievable:
--   $$Q=\tfrac12I(A:R),\qquad E=\tfrac12I(A:B).$$
--   Here $Q$ is qubits sent per source copy and $E$ is generated ebits per copy. Vanishing trace-norm error is tested jointly against the relocated source, the passive reference, and the output Bell state. Every achievable pair has qubit rate at least $Q$, and among pairs at that minimum qubit rate the generated entanglement rate is at most $E$. This is the operational resource inequality (44), including its stated optimality; zero rates permit sublinear resources.
-- source:
--   Quantum state merging and negative information, arXiv:quant-ph/0512247v1, PDF p. 10, Fully quantum merging (mother protocol), eq.(44), with optimal qubit cost and yield

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P01

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply finTransport referenceInformation)

open QAlgorithms.Papers.Independent.Bridge50.P40
  (RankMergingCode OneWayMergingCode mergingFidelity SourceProtocolAchievable)

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRA marginalRB motherTarget motherOutput sourceCopies swap mutualInformation)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Advance50.P29 (weakTypicalProjector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.10--11, (44) and its optimality paragraphs: joint source
transfer and EPR generation, minimum qubit cost and maximum yield at that cost. -/
theorem fully_quantum_merging {A B R : Type}
    [Fintype A] [Fintype B] [Fintype R] [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi) :
    let q := referenceInformation psi / 2
    let e := mutualInformation (traceLeft (pureDensity psi)) / 2
    MotherAchievable psi q e ∧
    (∀ q2 e2 : ℝ, MotherAchievable psi q2 e2 → q ≤ q2) ∧
    (∀ e2 : ℝ, MotherAchievable psi q e2 → e2 ≤ e) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P01

end
