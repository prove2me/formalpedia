-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_strong_converse_specializations
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.strong_converse_specializations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:34:00.403765+00:00
-- url     : https://prove2.me/theorems/e31cdabc-3aea-4dbd-b025-0cbd09c115d7
-- title:
--   Corollary 15: Strong converse specializations
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. For any block size $n$, let $\widehat\alpha_n(\mu;\rho,\tau)$ be the minimum rejection probability $\operatorname{tr}[(1-Q)\rho_{AB}^{\otimes n}]$ over all joint effects $0\le Q\le1$ satisfying $\sup_{\sigma_{B^n}\in\mathcal S(B^n)}\operatorname{tr}[Q(\tau_A^{\otimes n}\otimes\sigma_{B^n})]\le\mu$. The alternatives include every correlated block state. Limits run through positive integers and $-\log0=+\infty$. Let $\rho_{AB}$ be a state. Set $\widetilde I_s^\downarrow=\widetilde I_s(\rho\|\rho_A)$, $\widetilde H_s^\uparrow=-\widetilde I_s(\rho\|1_A)$, and $\pi_A=1_A/|A|$. The two conclusions have separate rate domains:
--   $$\lim_n-\frac1n\log[1-\widehat\alpha_n(e^{-nR};\rho,\rho_A)]=\sup_{s>1}\frac{s-1}{s}[R-\widetilde I_s^\downarrow]\quad(0<R<\widetilde I_\infty^\downarrow),$$
--   $$\lim_n-\frac1n\log[1-\widehat\alpha_n(e^{-nR};\rho,\pi_A)]=\sup_{s>1}\frac{s-1}{s}[R-\log|A|+\widetilde H_s^\uparrow]\quad(0<R<\widetilde I_\infty(\rho\|\pi_A)).$$
--   These are the two operational specializations; neither requires the rate to lie below both thresholds simultaneously.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 15, Corollary 15: Strong converse specializations

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

/-- arXiv:1408.6894v5, PDF p.15, Corollary 15, BOTH (6.2) and (6.3).
Each conclusion has its OWN rate threshold; no intersection is imposed. -/
theorem strong_converse_specializations [Nonempty A] [Nonempty B]
    (rho : Op (A × B)) (hr : IsDensityMatrix rho) :
    (∀ R : ℝ, 0 < R → (R : EReal) < marginalReferenceInformation true ⊤ rho →
      Tendsto (fun k : ℕ => normalizedErrorExponent (k+1) (1-exponentialCompositeError rho (traceRight rho) (k+1) R)) atTop
        (𝓝 (⨆ s : {s : ℝ // 1 < s},
          (((s.val-1)/s.val : ℝ) : EReal) * ((R : EReal) - marginalReferenceInformation true (s.val : RenyiOrder) rho)))) ∧
    (∀ R : ℝ, 0 < R → (R : EReal) < generalizedInformation true ⊤ rho (mixed A) →
      Tendsto (fun k : ℕ => normalizedErrorExponent (k+1) (1-exponentialCompositeError rho (mixed A) (k+1) R)) atTop
        (𝓝 (⨆ s : {s : ℝ // 1 < s},
          (((s.val-1)/s.val : ℝ) : EReal) *
            ((R : EReal) - (Real.log (Fintype.card A) : EReal) + optimizedConditionalEntropy true (s.val : RenyiOrder) rho)))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
