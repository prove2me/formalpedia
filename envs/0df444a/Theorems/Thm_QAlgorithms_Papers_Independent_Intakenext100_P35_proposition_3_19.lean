-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_proposition_3_19
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.proposition_3_19
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:18:51.684993+00:00
-- url     : https://prove2.me/theorems/7de48156-f41b-4c71-9b01-82c2d6d16003
-- title:
--   Proposition 3.19
-- statement:
--   For $t\ge0$ let $\varphi_t(z)=z(1+z)^{-1}e^{-t/z}$, a Laplace transform of a finite complex measure. There are positive constants and thresholds greater than one such that, for all sufficiently large $t$,
--
--   $$\|\varphi_t\|_{\mathrm{HP}}\lesssim t,\qquad\|\varphi_t\|_{\mathcal B}\asymp\log t.$$
--
--   Only the Besov comparison is two-sided. These scalar bounds motivate the inverse-generator estimate.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 17, Proposition 3.19

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Proposition 3.19, arXiv:2202.03143v1, PDF page(s) 17. -/
theorem proposition_3_19
:
    (∀ t : ℝ, 0 ≤ t → LM (phiSymbol t)) ∧
    (∃ C T : ℝ, 0 < C ∧ 1 < T ∧ ∀ t : ℝ, T ≤ t →
      hpSize (phiSymbol t) ≤ ENNReal.ofReal (C * t)) ∧
    (∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ 1 < T ∧ ∀ t : ℝ, T ≤ t →
      ENNReal.ofReal (c * Real.log t) ≤ bSize (phiSymbol t) ∧
      bSize (phiSymbol t) ≤ ENNReal.ofReal (C * Real.log t)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
