-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_inequalityEquivalences
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.inequalityEquivalences
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:58:14.782528+00:00
-- url     : https://prove2.me/theorems/4fe6974d-4d1a-4fe5-b8dc-04e47acb823c
-- title:
--   Section 5.3: relationships among MONO, MPT, SSA and JC
-- statement:
--   Let MONO, MPT, SSA and JC denote the universal finite-dimensional principles of relative-entropy monotonicity under all CPTP maps, monotonicity under partial trace, strong subadditivity, and joint convexity, respectively. The relative-entropy principles include PSD support-included pairs and unnormalized references; SSA ranges over normalized PSD states. Then
--   $$\mathrm{MONO}\Rightarrow\mathrm{MPT},\qquad\mathrm{MPT}\Longleftrightarrow\mathrm{SSA}\Longleftrightarrow\mathrm{JC},\qquad\mathrm{MPT}\Rightarrow\mathrm{MONO}.$$
--   These are relationships among global principles, including the singular block and dilation cases used in their reductions. Equality characterizations are not part of these principles.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 15, Section 5.3: relationships among MONO, MPT, SSA and JC

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P51

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakethird100.P51

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact interfaces from the frozen accepted library; no local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy marginalAB channelAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAC)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Gap48.P33 (measurementInformation)

section Statements

variable {A B C D J K O : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype J] [Fintype K] [Fintype O]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq J] [DecidableEq K] [DecidableEq O]

/-- Section 5.3, equation (37) and Lindblad's completion, PDF pp.14–15:
relationships between the four GLOBAL principles, including PSD/support cases. -/
theorem inequalityEquivalences :
    (MONO → MPT) ∧ (MPT ↔ SSA) ∧ (SSA ↔ JC) ∧ (MPT → MONO) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
