-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P44_relative_entropy_orthogonal_mixture
-- name    : QAlgorithms.Papers.Independent.Support50.P44.relative_entropy_orthogonal_mixture
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T23:59:43.3624+00:00
-- url     : https://prove2.me/theorems/e84b955e-882f-4353-9cfb-376c288210ac
-- title:
--   Relative entropy of orthogonal mixtures
-- statement:
--   Let $\rho,\rho',\sigma,\sigma'$ be density operators on a complex separable Hilbert space. Assume each of $\rho,\sigma$ is orthogonal to each of $\rho',\sigma'$. For $p\in[0,1]$, let $D$ denote Umegaki relative entropy in bits, allowing $+\infty$. Then
--
--   $$D(p\rho+(1-p)\rho'\|p\sigma+(1-p)\sigma')=pD(\rho\|\sigma)+(1-p)D(\rho'\|\sigma').$$
--
--   Here $0\cdot\infty=0$. This identity gives exact affinity of relative entropy across matched orthogonal blocks.
-- source:
--   Universal recovery map for approximate Markov chains, arXiv:1504.07251v3, PDF p. 24, Lemma B.2

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

/-- PDF p.24, Lemma B.2, (147): orthogonal-block affinity of extended Umegaki
entropy. ENNReal multiplication makes 0 times infinity zero at p = 0 or 1. -/
theorem relative_entropy_orthogonal_mixture {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (rho rho2 sigma sigma2 : H →L[ℂ] H)
    (hrho : IsHilbertDensity b rho) (hrho2 : IsHilbertDensity b rho2)
    (hsigma : IsHilbertDensity b sigma) (hsigma2 : IsHilbertDensity b sigma2)
    (horth : OrthogonalBlocks rho rho2 sigma sigma2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    hilbertRelativeEntropy (hilbertMix p rho rho2) (hilbertMix p sigma sigma2) =
      ENNReal.ofReal p * hilbertRelativeEntropy rho sigma +
        ENNReal.ofReal (1-p) * hilbertRelativeEntropy rho2 sigma2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P44

end
