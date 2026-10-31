-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P61_haarReal_half_inner_interval
-- name    : QAlgorithms.Papers.Independent.Intake100.P61.haarReal_half_inner_interval
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:02:31.310995+00:00
-- url     : https://prove2.me/theorems/b78ccfbb-1e96-4c54-acdf-753e7566b0a4
-- title:
--   Lemma 8: common real half-projection inner-product concentration
-- statement:
--   Let $n>0$, let $X,Y\in\mathbb R^{4n}$ be fixed, and let $P$ be a common orthogonal projector onto one Haar-uniform real $2n$-dimensional subspace. For $0\le x\le n/2$, put $S=\|X\|^2+\|Y\|^2$. Then
--
--   $$\Pr\!\left[\langle X,Y\rangle-1.85\sqrt{x/n}\,S\le 2\langle PX,PY\rangle\le\langle X,Y\rangle+1.85\sqrt{x/n}\,S\right]\ge1-8e^{-x}.$$
--
--   The same projection acts on both vectors, and zero vectors are allowed. The result controls the correlation in one virtual half.
-- source:
--   Composable security proof for continuous-variable quantum key distribution with coherent states, arXiv:1408.5689v3, PDF p. 21, Lemma 8, E6

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P61

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P61

attribute [local instance] Classical.propDecidable Classical.decEq

-- The frozen frequency formula specializes exactly to the source alphabet Fin (2 ^ d).

open QAlgorithms.Papers.Independent.Advance50.P30 (empiricalFrequency)

/-- PDF p.21, Lemma 8 (E6): one common real Haar subspace for both vectors.
Zero vectors are included; x has the nonnegative square-root domain. -/
theorem haarReal_half_inner_interval
    (n : ℕ) (hn : 0 < n) (X Y : Fin (4 * n) → ℝ)
    (mu : Measure (Matrix.unitaryGroup (Fin (4 * n)) ℝ))
    [IsProbabilityMeasure mu] [Measure.IsMulLeftInvariant mu]
    (x : ℝ) (hx : 0 ≤ x) (hxmax : x ≤ (n : ℝ) / 2) :
    ENNReal.ofReal (1 - 8 * Real.exp (-x)) ≤
      mu {U | realDot X Y - 1.85 * Real.sqrt (x / n) *
          (vectorSquare X + vectorSquare Y) ≤
          2 * realDot (halfProjection U (2 * n) X) (halfProjection U (2 * n) Y) ∧
        2 * realDot (halfProjection U (2 * n) X) (halfProjection U (2 * n) Y) ≤
          realDot X Y + 1.85 * Real.sqrt (x / n) *
          (vectorSquare X + vectorSquare Y)} := by sorry

end QAlgorithms.Papers.Independent.Intake100.P61

end
