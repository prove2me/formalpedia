-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_dataProcessingEquality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.dataProcessingEquality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:00:15.064498+00:00
-- url     : https://prove2.me/theorems/6eca5de9-0373-4bd7-9c20-faa8be59bc8e
-- title:
--   Theorem 8: adjoint logarithm characterization of equality
-- statement:
--   Let $\Phi$ be a finite CPTP map and let $\rho,\gamma>0$ be normalized input states. Define $L=\log\Phi(\rho)-\log\Phi(\gamma)$ on their common output support and extend $L$ by zero to its orthogonal complement. Let $\widehat\Phi$ be the actual Hilbert–Schmidt adjoint. Then
--   $$H(\Phi(\rho),\Phi(\gamma))=H(\rho,\gamma)\iff\log\rho-\log\gamma=\widehat\Phi(L).$$
--   This is the adjoint-logarithm characterization of equality, preserving all finite channels and using compressed output calculus.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 15, Theorem 8: adjoint logarithm characterization of equality

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

/-- Theorem 8, equation (40), PDF pp.15–17: actual adjoint and supported output
logarithms. For faithful inputs the two outputs have common support supp(Phi I),
so the cfc log difference is the unique zero extension from this support. -/
theorem dataProcessingEquality [Nonempty A] [Nonempty B] (Phi : Superop A B) (hPhi : IsChannel Phi) (rho gamma : Mat A)
    (hr : FaithfulDensity rho) (hg : FaithfulDensity gamma) :
    (relativeEntropy (Phi rho) (Phi gamma)).toReal = (relativeEntropy rho gamma).toReal ↔
      logMatrix rho - logMatrix gamma =
        channelAdjoint Phi (logMatrix (Phi rho) - logMatrix (Phi gamma)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
