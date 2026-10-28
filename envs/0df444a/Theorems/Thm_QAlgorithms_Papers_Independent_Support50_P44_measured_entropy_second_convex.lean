-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P44_measured_entropy_second_convex
-- name    : QAlgorithms.Papers.Independent.Support50.P44.measured_entropy_second_convex
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-24T00:02:03.022845+00:00
-- url     : https://prove2.me/theorems/60a5775d-01b9-4e4b-8c80-2b1f63862eff
-- title:
--   Convexity of measured relative entropy in the second input
-- statement:
--   Let $\rho,\sigma,\sigma'$ be density operators on a complex separable Hilbert space and $p\in[0,1]$. Define $D_M$ as the supremum of classical relative entropy in bits over finite-outcome POVMs. Then
--
--   $$D_M(\rho\|p\sigma+(1-p)\sigma')\le pD_M(\rho\|\sigma)+(1-p)D_M(\rho\|\sigma').$$
--
--   Values may be infinite and $0\cdot\infty=0$. No orthogonality is required. This inequality yields concavity of recovery slack in the recovery map.
-- source:
--   Universal recovery map for approximate Markov chains, arXiv:1504.07251v3, PDF p. 25, Lemma B.4

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

/-- PDF p.25, Lemma B.4, (155): convexity in the second input, without orthogonality. -/
theorem measured_entropy_second_convex {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (rho sigma sigma2 : H →L[ℂ] H)
    (hrho : IsHilbertDensity b rho) (hsigma : IsHilbertDensity b sigma)
    (hsigma2 : IsHilbertDensity b sigma2) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    measuredRelativeEntropy b rho (hilbertMix p sigma sigma2) ≤
      ENNReal.ofReal p * measuredRelativeEntropy b rho sigma +
        ENNReal.ofReal (1-p) * measuredRelativeEntropy b rho sigma2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P44

end
