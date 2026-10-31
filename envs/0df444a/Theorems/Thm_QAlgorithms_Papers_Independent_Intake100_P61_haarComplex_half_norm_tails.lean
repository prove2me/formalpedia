-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P61_haarComplex_half_norm_tails
-- name    : QAlgorithms.Papers.Independent.Intake100.P61.haarComplex_half_norm_tails
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:01:34.358882+00:00
-- url     : https://prove2.me/theorems/f6d53e14-fc68-4798-8ff2-3496722b1124
-- title:
--   Lemma 7: Haar complex half-projection norm concentration
-- statement:
--   Let $n>0$, let $X\ne0$ be a fixed vector in $\mathbb C^{2n}$, and let $P$ be orthogonal projection onto a Haar-uniform complex $n$-dimensional subspace. If $2e^{-n/2}\le\epsilon\le1$, set $t=\sqrt{\ln(2/\epsilon)/n}$. Then
--
--   $$\Pr[2\|PX\|^2\ge(1+1.5t)\|X\|^2]\le\epsilon,\qquad
--   \Pr[2\|PX\|^2\le(1-2.2t)\|X\|^2]\le\epsilon.$$
--
--   These bounds control the norm in one virtual half. **Source correction:** E3 prints $\ln(2\epsilon)$; the proof uses the common parameter $\ln(2/\epsilon)$. The zero vector is excluded because the proof normalizes it and the printed inclusive events are otherwise certain. Independent moderation remains pending.
-- source:
--   Composable security proof for continuous-variable quantum key distribution with coherent states, arXiv:1408.5689v3, PDF p. 20, Lemma 7, E2–E3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P61

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P61

attribute [local instance] Classical.propDecidable Classical.decEq

-- The frozen frequency formula specializes exactly to the source alphabet Fin (2 ^ d).

open QAlgorithms.Papers.Independent.Advance50.P30 (empiricalFrequency)

/-- PDF pp.20–21, Lemma 7 (E2–E3), corrected: E3 prints ln(2 epsilon);
the proof's common deviation parameter requires ln(2/epsilon). X is nonzero:
the proof normalizes X, and both inclusive events are certain at zero.
These corrections require independent moderation. -/
theorem haarComplex_half_norm_tails
    (n : ℕ) (hn : 0 < n) (X : Fin (2 * n) → ℂ) (hX : X ≠ 0)
    (mu : Measure (Matrix.unitaryGroup (Fin (2 * n)) ℂ))
    [IsProbabilityMeasure mu] [Measure.IsMulLeftInvariant mu]
    (epsilon : ℝ) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hregime : 2 * Real.exp (-(n : ℝ) / 2) ≤ epsilon) :
    mu {U | 2 * vectorSquare (halfProjection U n X) ≥
      (1 + 1.5 * Real.sqrt (Real.log (2 / epsilon) / n)) * vectorSquare X} ≤
        ENNReal.ofReal epsilon ∧
    mu {U | 2 * vectorSquare (halfProjection U n X) ≤
      (1 - 2.2 * Real.sqrt (Real.log (2 / epsilon) / n)) * vectorSquare X} ≤
        ENNReal.ofReal epsilon := by sorry

end QAlgorithms.Papers.Independent.Intake100.P61

end
