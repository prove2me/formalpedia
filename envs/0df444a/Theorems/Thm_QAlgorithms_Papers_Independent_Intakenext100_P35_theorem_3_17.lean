-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_theorem_3_17
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.theorem_3_17
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:17:57.096078+00:00
-- url     : https://prove2.me/theorems/49b469de-a670-439a-8565-a917985b0ba8
-- title:
--   Theorem 3.17
-- statement:
--   Suppose $-A$ generates a bounded C0-semigroup on a Hilbert space. For $f\in\mathcal B\cap C_0(\overline{\mathbb C_+})$,
--
--   $$\sigma(f(A))\cup\{0\}=f(\sigma(A))\cup\{0\}.$$
--
--   In particular this holds for $f=\mathcal L\mu$ whenever the Fourier transform of the finite complex measure $\mu$ vanishes at infinity. The adjoined zero is essential to the asserted equality.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 15, Theorem 3.17

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Theorem 3.17, arXiv:2202.03143v1, PDF page(s) 15. -/
theorem theorem_3_17
{X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
(A : DenseClosedGraphOperator X) (hA : HilbertGenerator A) :
    (∀ f, BesovClass f → Vanishes f → spectrum ℂ (bOperator A f) ∪ {0} =
      (extension hp f) '' operatorSpectrum A ∪ {0}) ∧
    (∀ mu w f, LaplaceRep mu w f →
      Tendsto (fun b : ℝ => ∫ t, Complex.exp (-Complex.I * (b : ℂ) * (t : ℂ)) * w t ∂mu)
        (Filter.comap (fun b : ℝ => |b|) atTop) (𝓝 0) →
      spectrum ℂ (bOperator A f) ∪ {0} = (extension hp f) '' operatorSpectrum A ∪ {0}) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
