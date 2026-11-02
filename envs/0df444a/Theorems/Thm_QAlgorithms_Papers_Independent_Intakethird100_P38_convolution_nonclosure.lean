-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_convolution_nonclosure
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.convolution_nonclosure
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:29:44.719181+00:00
-- url     : https://prove2.me/theorems/5248618d-829c-4354-a5b1-9eb8a0be5f00
-- title:
--   The spectral measure class is not closed under self-convolution
-- statement:
--   On $\mathbb R$, let $\lambda$ be ordinary Lebesgue measure. For positive measures, define $\sigma\star\tau$ as the pushforward of $\sigma\times\tau$ under addition, allowing extended masses. Let $\mathcal C$ be the regular positive Borel measures with $\int(1+u^2)^{-p}\,d\sigma(u)<\infty$ for some nonnegative integer $p$. Then
--
--   $$\lambda\in\mathcal C,\qquad\lambda\star\lambda\notin\mathcal C.$$
--
--   Thus $\mathcal C$ is not stable under self-convolution. The extended convolution measure exists; it is not locally finite and has infinite weighted mass, rather than being nonexistent as claimed in the source's stronger rhetoric.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 25, §11, unnumbered: C is not closed under self-convolution

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- §11, PDF p.25: Lebesgue measure belongs to C, but its self-convolution does not.
The pushforward still exists as an extended measure, contrary to the source's
stronger “not a well defined Borel measure” rhetoric. -/
theorem convolution_nonclosure :
    InC (volume : Measure (SpectralDomain 1)) ∧
      ¬ InC (measureConvolution (volume : Measure (SpectralDomain 1)) volume) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
