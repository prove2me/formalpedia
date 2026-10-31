-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P01_merging_classical_cost
-- name    : QAlgorithms.Papers.Independent.Intake100.P01.merging_classical_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:53:54.882091+00:00
-- url     : https://prove2.me/theorems/f31c0747-e2aa-4c0c-999a-c01f494ad7a6
-- title:
--   Theorem 8: optimal classical communication for merging
-- statement:
--   Let $|\psi\rangle_{ABR}$ be a unit vector on finite nonzero registers. Among all asymptotic LOCC merging protocols with vanishing complete-output error and any finite signed entanglement rate, count the maximum total number of transmitted classical bits in both directions, divided by blocklength. Its smallest achievable limiting rate is
--   $$C_{\mathrm{merge}}=I(A:R)=S(A)+S(R)-S(AR).$$
--   The minimum is achievable in rate closure and every achievable rate is at least this value. The purifying reference remains untouched and final Bell resources are tested jointly with the relocated source. This gives the communication optimum independently of imposing an optimal entanglement cost.
-- source:
--   Quantum state merging and negative information, arXiv:quant-ph/0512247v1, PDF p. 10, Theorem 8: optimal classical communication for merging

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

/-- PDF pp.10--11, Theorem 8: the minimum TOTAL transmitted classical-bit
rate over adaptive LOCC is I(A:R), regardless of the finite signed EPR rate. -/
theorem merging_classical_cost {A B R : Type}
    [Fintype A] [Fintype B] [Fintype R] [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi) :
    IsLeast {c : ℝ | ClassicalMergingAchievable psi c} (referenceInformation psi) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P01

end
