-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_discrete_gaussian_overlap
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.discrete_gaussian_overlap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:17:19.229097+00:00
-- url     : https://prove2.me/theorems/8451cba4-97e2-4da9-ba36-d9741e0f37b9
-- title:
--   Lemma 11: discrete Gaussian overlap, Eq.(D.32)
-- statement:
--   Let $w>0$, and let $x,h$ be integers with $|x|\le h$ and $h$ even. Define $c_w=\sum_{y\in\mathbb Z}e^{-y^2/(2w^2)}$. For either sign, $$\frac1{c_w}\sum_{y\in\mathbb Z}\exp\!\left(-\frac{(y\pm x)^2+y^2}{4w^2}\right)\ge\exp\!\left(-\frac{h^2}{8w^2}\right).$$ All Gaussian series converge for $w>0$. This controls overlaps of shifted normalized Gaussian codewords.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 44, Lemma 11: discrete Gaussian overlap, Eq.(D.32)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF pp.44–45, Lemma 11, (D.32). Even h is essential for the odd-x endpoint. -/
theorem discrete_gaussian_overlap (w : ℝ) (hw : 0 < w) (h x : ℤ)
    (hx : |x| ≤ h) (heven : Even h) :
    ∀ s : ℤ, (s = 1 ∨ s = -1) →
      Real.exp (-((h : ℝ) ^ 2) / (8 * w ^ 2)) ≤
        (∑' y : ℤ, Real.exp (-(((y : ℝ) + s * x) ^ 2 + (y : ℝ) ^ 2) / (4 * w ^ 2))) /
          gaussianNormalization w := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
