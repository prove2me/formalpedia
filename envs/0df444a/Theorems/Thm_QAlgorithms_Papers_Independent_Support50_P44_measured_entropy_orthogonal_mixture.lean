-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P44_measured_entropy_orthogonal_mixture
-- name    : QAlgorithms.Papers.Independent.Support50.P44.measured_entropy_orthogonal_mixture
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-24T00:01:06.170717+00:00
-- url     : https://prove2.me/theorems/00303133-7ada-4806-a0f7-d0d37a87cb1b
-- title:
--   Measured relative entropy of orthogonal mixtures
-- statement:
--   Let $\rho,\rho',\sigma,\sigma'$ be density operators on a complex separable Hilbert space, with each of $\rho,\sigma$ orthogonal to each of $\rho',\sigma'$. Let $D_M$ be the supremum, over all finite-outcome POVMs, of the classical relative entropy in bits of the two resulting outcome laws. For $p\in[0,1]$,
--
--   $$D_M(p\rho+(1-p)\rho'\|p\sigma+(1-p)\sigma')=pD_M(\rho\|\sigma)+(1-p)D_M(\rho'\|\sigma').$$
--
--   Infinite values are retained, with $0\cdot\infty=0$. The result does not require the supremum to be attained and supplies the orthogonal-block identity used for flagged extensions.
-- source:
--   Universal recovery map for approximate Markov chains, arXiv:1504.07251v3, PDF p. 24, Lemma B.3

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P44

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass compression)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Renew46.P37 (classicalKL)

open Filter

open scoped ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF pp.24–25, Lemma B.3, (149): affinity of the finite-POVM supremum.
There is no added optimal-measurement hypothesis. -/
theorem measured_entropy_orthogonal_mixture {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (rho rho2 sigma sigma2 : H →L[ℂ] H)
    (hrho : IsHilbertDensity b rho) (hrho2 : IsHilbertDensity b rho2)
    (hsigma : IsHilbertDensity b sigma) (hsigma2 : IsHilbertDensity b sigma2)
    (horth : OrthogonalBlocks rho rho2 sigma sigma2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    measuredRelativeEntropy b (hilbertMix p rho rho2) (hilbertMix p sigma sigma2) =
      ENNReal.ofReal p * measuredRelativeEntropy b rho sigma +
        ENNReal.ofReal (1-p) * measuredRelativeEntropy b rho2 sigma2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P44

end
