-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_lemma_3_11
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.lemma_3_11
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:15:44.161744+00:00
-- url     : https://prove2.me/theorems/5139b703-4069-4518-b0a7-161e25668116
-- title:
--   Lemma 3.11
-- statement:
--   Let $\mu$ be a finite complex measure on $[0,\infty)$ with total mass one and finite first absolute moment, and put $m=\mathcal L\mu$. For $f\in\mathcal B$ define $f_\delta(z)=m(\delta z)f(z)$. For every $g\in\mathcal E$,
--
--   $$\langle g,f_\delta\rangle_{\mathcal B}\longrightarrow\langle g,f\rangle_{\mathcal B}\qquad(\delta\downarrow0).$$
--
--   This gives weak approximation in the partial Besov duality.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 12, Lemma 3.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Lemma 3.11, arXiv:2202.03143v1, PDF page(s) 12. -/
theorem lemma_3_11
(mu : Measure ℝ) (w : ℝ → ℂ) (m f : AnalyticSymbol)
(hrep : LaplaceRep mu w m) (hmass : (∫ t, w t ∂mu) = 1)
(hmoment : Integrable (fun t => t * ‖w t‖) mu) (hf : BesovClass f) :
    ∀ g, DerivativeDualClass g → Tendsto
      (fun delta : ℝ => besovPairing g (fun z => m ((delta : ℂ) * z) * f z))
      (𝓝[>] 0) (𝓝 (besovPairing g f)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
