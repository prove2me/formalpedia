-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_proposition_3_1
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.proposition_3_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:12:05.934995+00:00
-- url     : https://prove2.me/theorems/322f63be-1542-4940-b2dd-e4ce0724d396
-- title:
--   Proposition 3.1
-- statement:
--   Let $f$ be holomorphic on $\mathbb C_+$ with finite Besov derivative seminorm. It has a limit $f(\infty)$ as $\operatorname{Re}z\to\infty$, is bounded, has boundary limits uniformly along the imaginary axis, and its extension to the closed half-plane is uniformly continuous. Moreover,
--
--   $$\|f\|_\infty\le |f(\infty)|+\|f\|_{\mathcal B_0}.$$
--
--   This supplies the boundary and infinity values used throughout the calculus.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 7, Proposition 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Proposition 3.1, arXiv:2202.03143v1, PDF page(s) 7. -/
theorem proposition_3_1
(f : AnalyticSymbol) (hf : BesovClass f) :
    Tendsto f (Filter.comap Complex.re atTop) (𝓝 (infinityValue f)) ∧
    HInfinity hp f ∧ supSize hp f ≤ ENNReal.ofReal ‖infinityValue f‖ + bSemi f ∧
    (∀ eps : ℝ, 0 < eps → ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a < d →
      ∀ b : ℝ, ‖f (point a b) - extension hp f (point 0 b)‖ < eps) ∧
    EqOn (extension hp f) f hp ∧ UniformContinuousOn (extension hp f) closedHp := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
