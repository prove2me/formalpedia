-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_dataProcessing
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.dataProcessing
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:59:08.791878+00:00
-- url     : https://prove2.me/theorems/3d39eaa8-6765-4aa7-b907-c8b003e4c3db
-- title:
--   Equation (7), proved in Section 5.3: CPTP data processing
-- statement:
--   Let $\Phi$ be any finite CPTP map, possibly between different dimensions, and let $\rho,\gamma>0$ be normalized states. Then
--   $$H(\Phi(\rho),\Phi(\gamma))\le H(\rho,\gamma).$$
--   The outputs are faithful on their common support $\operatorname{supp}\Phi(I)$; output logarithms are evaluated there. Thus channels with singular ambient outputs, including pure-state replacers, are included. This is quantum data processing.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 4, Equation (7), proved in Section 5.3: CPTP data processing

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

/-- Equation (7), PDF pp.4,15,17: all finite CPTP maps, including singular-output
and rectangular channels. Common-support calculus evaluates the output entropy. -/
theorem dataProcessing [Nonempty A] [Nonempty B] (Phi : Superop A B) (hPhi : IsChannel Phi) (rho gamma : Mat A)
    (hr : FaithfulDensity rho) (hg : FaithfulDensity gamma) :
    (relativeEntropy (Phi rho) (Phi gamma)).toReal ≤ (relativeEntropy rho gamma).toReal := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
