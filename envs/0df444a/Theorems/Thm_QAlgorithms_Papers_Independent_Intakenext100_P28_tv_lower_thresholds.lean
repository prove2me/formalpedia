-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_tv_lower_thresholds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.tv_lower_thresholds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:37:03.818958+00:00
-- url     : https://prove2.me/theorems/f2a8567e-81c4-412c-ba16-c0728e8e3b5a
-- title:
--   Theorem 20: For every beta0 in (0,1), TV>=2(1-beta0)P_Q(i<log beta0), and TV>=2(1-beta0)P_P(i>log(1/beta0))
-- statement:
--   For every probability pair $P\ll Q$ and every $0<t<1$, with $I=\log_b(dP/dQ)$,
--
--   $$|P-Q|\ge2(1-t)Q[I<\log_b t],\qquad
--   |P-Q|\ge2(1-t)P[I>\log_b(1/t)].$$
--
--   These are the two strict-threshold spectrum lower bounds (272)–(273).
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 38, Theorem 20

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 20: For every beta0 in (0,1), TV>=2(1-beta0)P_Q(i<log beta0), and TV>=2(1-beta0)P_P(i>log(1/beta0)). Sason--Verdu, arXiv:1508.00335v7, PDF p.38.  -/
theorem tv_lower_thresholds
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (t : ℝ) (ht : 0 < t ∧ t < 1) :
    2 * ENNReal.ofReal (1 - t) * Q {x | relativeInfo b P Q x < elogB b (ENNReal.ofReal t)} ≤ fullVariation P Q ∧
    2 * ENNReal.ofReal (1 - t) * P {x | elogB b ((ENNReal.ofReal t)⁻¹) < relativeInfo b P Q x} ≤ fullVariation P Q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
