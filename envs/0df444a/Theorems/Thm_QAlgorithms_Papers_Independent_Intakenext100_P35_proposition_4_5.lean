-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_proposition_4_5
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.proposition_4_5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:22:10.330433+00:00
-- url     : https://prove2.me/theorems/7a281934-d2e6-41df-a560-306b19d6ba59
-- title:
--   Proposition 4.5
-- statement:
--   For $-1<s<\sigma$, the two integral operators have distinct bounded linear mapping properties:
--
--   $$Q_\sigma:\mathcal V_s\longrightarrow\mathcal D_s,\qquad Q_s:\mathcal V_s\longrightarrow\mathcal D_\sigma.$$
--
--   Each bound has a constant depending only on the two exponents. The target spaces cannot be interchanged.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 20, Proposition 4.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Proposition 4.5, arXiv:2202.03143v1, PDF page(s) 20. -/
theorem proposition_4_5
(s sigma : ℝ) (hs : -1 < s) (hss : s < sigma) :
    (∃ C : ℝ, 0 < C ∧ ∀ g, WeightedDerivativeClass s g → D s (Qs sigma g) ∧
      dSize s (Qs sigma g) ≤ ENNReal.ofReal C * vSize s g) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ g, WeightedDerivativeClass s g → D sigma (Qs s g) ∧
      dSize sigma (Qs s g) ≤ ENNReal.ofReal C * vSize s g) ∧
    (∀ c : ℂ, ∀ g h, WeightedDerivativeClass s g → WeightedDerivativeClass s h →
      EqOn (Qs sigma (c • g + h)) (c • Qs sigma g + Qs sigma h) hp ∧
      EqOn (Qs s (c • g + h)) (c • Qs s g + Qs s h) hp) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
