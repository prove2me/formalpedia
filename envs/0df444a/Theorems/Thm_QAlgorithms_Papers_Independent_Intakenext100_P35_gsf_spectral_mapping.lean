-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_gsf_spectral_mapping
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.gsf_spectral_mapping
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:28:26.640875+00:00
-- url     : https://prove2.me/theorems/41745606-e9d7-4016-94c5-458900708a58
-- title:
--   Section 3 Application 1: GSF spectral mapping extension
-- statement:
--   For every closed densely defined operator $A$ satisfying GSF on a complex Banach space and every $f\in\mathcal B\cap C_0(\overline{\mathbb C_+})$,
--
--   $$\sigma(f(A))\cup\{0\}=f(\sigma(A))\cup\{0\}.$$
--
--   This is the explicit GSF extension following Theorem 3.17, with the same vanishing algebra and the same adjoined zero.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 15, Section 3 Application 1: GSF spectral mapping extension

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Section 3 Application 1: GSF spectral mapping extension, arXiv:2202.03143v1, PDF page(s) 15. -/
theorem gsf_spectral_mapping
{X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
(A : DenseClosedGraphOperator X) (hA : GSF A) (f : AnalyticSymbol) (hf : BesovClass f) (hv : Vanishes f) :
    spectrum ℂ (bOperator A f) ∪ {0} =
      (extension hp f) '' operatorSpectrum A ∪ {0} := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
