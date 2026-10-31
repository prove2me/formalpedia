-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_hoeffding_specializations
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.hoeffding_specializations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:31:49.071219+00:00
-- url     : https://prove2.me/theorems/8e27ac0e-13db-4c76-becf-0e7ba1301cf7
-- title:
--   Corollary 13: Hoeffding specializations: mutual information and conditional entropy
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. For any block size $n$, let $\widehat\alpha_n(\mu;\rho,\tau)$ be the minimum rejection probability $\operatorname{tr}[(1-Q)\rho_{AB}^{\otimes n}]$ over all joint effects $0\le Q\le1$ satisfying $\sup_{\sigma_{B^n}\in\mathcal S(B^n)}\operatorname{tr}[Q(\tau_A^{\otimes n}\otimes\sigma_{B^n})]\le\mu$. The alternatives include every correlated block state. Limits run through positive integers and $-\log0=+\infty$. Let $\rho_{AB}$ be a state and $R>0$. Define $I_s^\downarrow(A:B)_\rho=I_s(\rho\|\rho_A)$, $H_s^\uparrow(A|B)_\rho=-I_s(\rho\|1_A)$, and $\pi_A=1_A/|A|$. Both identities hold:
--   $$\lim_n-\frac1n\log\widehat\alpha_n(e^{-nR};\rho,\rho_A)=\sup_{0<s<1}\frac{1-s}{s}\left[I_s^\downarrow(A:B)_\rho-R\right],$$
--   $$\lim_n-\frac1n\log\widehat\alpha_n(e^{-nR};\rho,\pi_A)=\sup_{0<s<1}\frac{1-s}{s}\left[\log|A|-H_s^\uparrow(A|B)_\rho-R\right].$$
--   These give the mutual-information and conditional-entropy interpretations; the second testing reference is normalized.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 13, Corollary 13: Hoeffding specializations: mutual information and conditional entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P47

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Topology

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P28 (SupportLE pinch logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

open QAlgorithms.Papers.Independent.Claimed50.P12 (DiagonalIn)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D I J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq I] [DecidableEq J]

/-- arXiv:1408.6894v5, PDF p.13, Corollary 13, BOTH (5.2) and (5.3).
The optimizedConditionalEntropy-entropy test uses pi_A, the NORMALIZED maximally mixed state. -/
theorem hoeffding_specializations [Nonempty A] [Nonempty B]
    (rho : Op (A × B)) (hr : IsDensityMatrix rho) (R : ℝ) (hR : 0 < R) :
    Tendsto (fun k : ℕ => normalizedErrorExponent (k+1) (exponentialCompositeError rho (traceRight rho) (k+1) R)) atTop
      (𝓝 (⨆ s : {s : ℝ // 0 < s ∧ s < 1},
        (((1-s.val)/s.val : ℝ) : EReal) * (marginalReferenceInformation false (s.val : RenyiOrder) rho - (R : EReal)))) ∧
    Tendsto (fun k : ℕ => normalizedErrorExponent (k+1) (exponentialCompositeError rho (mixed A) (k+1) R)) atTop
      (𝓝 (⨆ s : {s : ℝ // 0 < s ∧ s < 1},
        (((1-s.val)/s.val : ℝ) : EReal) *
          ((Real.log (Fintype.card A) : EReal) - optimizedConditionalEntropy false (s.val : RenyiOrder) rho - (R : EReal)))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
