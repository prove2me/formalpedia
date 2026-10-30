-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_displacementCharacteristic
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.displacementCharacteristic
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:49:57.69691+00:00
-- url     : https://prove2.me/theorems/082eb5ed-a36a-4f34-bd45-a5c40c5a5be3
-- title:
--   Appendix B, Eqs.(B1)–(B2): displacement-channel characteristic function
-- statement:
--   Let $s\ge0$. The Gaussian displacement channel $\mathcal B_s$ is the complex displacement average with density $e^{-|\alpha|^2/s}/(\pi s)$ when $s>0$ and is the identity when $s=0$. For a trace-class oscillator input $X$ and $\xi=(\xi_q,\xi_p)\in\mathbb R^2$, define
--
--   $$\chi_X(\xi)=\operatorname{Tr}\!\left[X D\!\left(\frac{\xi_q+i\xi_p}{\sqrt2}\right)\right].$$
--
--   Then $\mathcal B_s$ is normal CPTP and
--
--   $$\chi_{\mathcal B_s(X)}(\xi)=e^{-s(\xi_q^2+\xi_p^2)/2}\chi_X(\xi).$$
--
--   Thus its Gaussian specification is $T=I_2$, $N=sI_2$, $d=0$. In particular each quadrature has added variance $s$, while each real coordinate of $\alpha$ has variance $s/2$. This fixes the displacement normalization used throughout the paper.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 16, Appendix B, Eqs.(B1)–(B2): displacement-channel characteristic function

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P16

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P16

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P32 (CPTP applyChoi)

/-- Appendix B, PDF p.16 Eqs.(B1)--(B2), Definition 3 p.2. Variance s in q,p
corresponds to variance s/2 in each real coordinate of complex displacement. -/
theorem displacementCharacteristic (s : ℝ) (hs : 0 ≤ s) :
    C.IsNormalFockChannel (C.displacementNoiseChannel s) ∧ B.DisplacementRealized ∧
    ∀ X, B.IsTraceClass X → ∀ xi : Fin 2 → ℝ,
      B.characteristic (C.displacementNoiseChannel s X)
        (((xi 0 : ℂ) + Complex.I * (xi 1 : ℂ)) / (Real.sqrt 2 : ℂ)) =
      B.characteristic X (((xi 0 : ℂ) + Complex.I * (xi 1 : ℂ)) / (Real.sqrt 2 : ℂ)) *
        (Real.exp (-s * ((xi 0) ^ 2 + (xi 1) ^ 2) / 2) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
