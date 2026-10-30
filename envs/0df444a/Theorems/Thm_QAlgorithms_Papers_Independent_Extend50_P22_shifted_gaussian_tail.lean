-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_shifted_gaussian_tail
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.shifted_gaussian_tail
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:18:27.942628+00:00
-- url     : https://prove2.me/theorems/bff953d3-aa84-4b76-b318-f6e21e58bd65
-- title:
--   Lemma 12: shifted Gaussian tail, Eq.(D.37), corrected cutoff domain
-- statement:
--   Let $w>0$ and let $W,x$ be integers with $W>|x|$. For either sign, $$\sum_{\substack{y\in\mathbb Z\\|y|>W}}e^{-(y\pm x)^2/(2w^2)}\le\frac{2w^2}{W-|x|}\exp\!\left(-\frac{(W-|x|)^2}{2w^2}\right).$$ This uses the proof’s integral cutoff and positive denominator. **Source correction:** the printed hypothesis $W\ge0$ alone is insufficient; the corrected domain follows (D.38) and the application. Independent moderation is still required.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 45, Lemma 12: shifted Gaussian tail, Eq.(D.37), corrected cutoff domain

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.45, Lemma 12, (D.37). SOURCE CORRECTION: printed W>=0 changed to integral
W>|x|, as required by the proof (D.38); otherwise the denominator can vanish or be negative.
The correction still requires independent moderation. -/
theorem shifted_gaussian_tail (w : ℝ) (hw : 0 < w) (W x : ℤ) (hW : |x| < W) :
    ∀ s : ℤ, (s = 1 ∨ s = -1) →
      (∑' y : ℤ, if W < |y| then
        Real.exp (-(((y : ℝ) + s * x) ^ 2) / (2 * w ^ 2)) else 0) ≤
      2 * w ^ 2 / ((W : ℝ) - |(x : ℝ)|) *
        Real.exp (-(((W : ℝ) - |(x : ℝ)|) ^ 2) / (2 * w ^ 2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
