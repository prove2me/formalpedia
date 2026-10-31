-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P61_haarReal_correlation_complement_tails
-- name    : QAlgorithms.Papers.Independent.Intake100.P61.haarReal_correlation_complement_tails
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:06:26.257328+00:00
-- url     : https://prove2.me/theorems/e19aa91c-fe86-4982-822c-79438512f92f
-- title:
--   E11–E12: projected-correlation and complementary-half tails
-- statement:
--   Let $n>0$ and let $X,Y\in\mathbb R^{4n}$ be fixed with $S=\|X\|^2+\|Y\|^2>0$. Let $P$ be a common Haar-uniform real projector of rank $2n$, and set $P^\perp=I-P$. For $0\le x\le n/2$,
--
--   $$\begin{aligned}
--   \Pr[\langle PX,PY\rangle\le\tfrac12\langle X,Y\rangle-\sqrt{x/n}\,S]&\le4e^{-x},\\
--   \Pr[|\langle PX,PY\rangle-\langle P^\perp X,P^\perp Y\rangle|\ge2\sqrt{x/n}\,S]&\le8e^{-x}.
--   \end{aligned}$$
--
--   The factor one half multiplies only the full inner product in the first bound. **Source correction:** the all-zero pair is excluded because the inclusive tail events would otherwise be certain for large $x$. Independent moderation remains pending.
-- source:
--   Composable security proof for continuous-variable quantum key distribution with coherent states, arXiv:1408.5689v3, PDF p. 21, E11–E12

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P61

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P61

attribute [local instance] Classical.propDecidable Classical.decEq

-- The frozen frequency formula specializes exactly to the source alphabet Fin (2 ^ d).

open QAlgorithms.Papers.Independent.Advance50.P30 (empiricalFrequency)

/-- PDF p.21, E11–E12: common real Haar P and its actual complement I-P.
The all-zero pair is excluded: the inclusive events would be certain while
4 exp(-x) and 8 exp(-x) can be <1. This correction needs independent moderation. -/
theorem haarReal_correlation_complement_tails
    (n : ℕ) (hn : 0 < n) (X Y : Fin (4 * n) → ℝ)
    (hXY : 0 < vectorSquare X + vectorSquare Y)
    (mu : Measure (Matrix.unitaryGroup (Fin (4 * n)) ℝ))
    [IsProbabilityMeasure mu] [Measure.IsMulLeftInvariant mu]
    (x : ℝ) (hx : 0 ≤ x) (hxmax : x ≤ (n : ℝ) / 2) :
    mu {U | realDot (halfProjection U (2 * n) X) (halfProjection U (2 * n) Y) ≤
      (1 / 2 : ℝ) * realDot X Y - Real.sqrt (x / n) *
        (vectorSquare X + vectorSquare Y)} ≤ ENNReal.ofReal (4 * Real.exp (-x)) ∧
    mu {U | |realDot (halfProjection U (2 * n) X) (halfProjection U (2 * n) Y) -
      realDot (X - halfProjection U (2 * n) X) (Y - halfProjection U (2 * n) Y)| ≥
        2 * Real.sqrt (x / n) * (vectorSquare X + vectorSquare Y)} ≤
      ENNReal.ofReal (8 * Real.exp (-x)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P61

end
