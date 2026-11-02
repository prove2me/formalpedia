-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_equalityIntertwining
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.equalityIntertwining
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:00:56.557204+00:00
-- url     : https://prove2.me/theorems/5326a568-8283-4049-b69a-8b5ff52f37d6
-- title:
--   Corollary 9: intertwining and Kraus-range commutation
-- statement:
--   Under equality in data processing for a finite CPTP map $\Phi$ and faithful normalized states $\rho,\gamma$, put $D=\log\rho-\log\gamma$ and let $L$ be the supported output log difference. Then
--   $$\Phi(D)=\Phi(I)L=L\Phi(I).$$
--   For every normalized Kraus representation $\Phi(X)=\sum_kF_kXF_k^{\dagger}$, form the computed isometry $V_{(a',k),a}=(F_k)_{a',a}$. Its range projection satisfies
--   $$[VV^{\dagger},L\otimes I_K]=0.$$
--   This records the intertwining and dilation-range commutation forced by equality.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 16, Corollary 9: intertwining and Kraus-range commutation

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

/-- Corollary 9, equations (45)–(46), PDF pp.16–17: the second operator is lifted
by I_K before commutation with the actual Kraus-range projection. -/
theorem equalityIntertwining [Nonempty A] [Nonempty B] [Nonempty K] (Phi : Superop A B) (hPhi : IsChannel Phi) (rho gamma : Mat A)
    (hr : FaithfulDensity rho) (hg : FaithfulDensity gamma)
    (he : (relativeEntropy (Phi rho) (Phi gamma)).toReal = (relativeEntropy rho gamma).toReal) :
    let D := logMatrix rho - logMatrix gamma
    let L := logMatrix (Phi rho) - logMatrix (Phi gamma)
    Phi D = Phi 1 * L ∧ Phi D = L * Phi 1 ∧
    ∀ F : K → Matrix B A ℂ, IsKrausFamily F → (∀ X, Phi X = krausApply F X) →
      (krausV F * (krausV F)ᴴ) * Matrix.kronecker L (1 : Mat K) =
        Matrix.kronecker L (1 : Mat K) * (krausV F * (krausV F)ᴴ) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
