-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P21_rectangle_thresholds_sharp
-- name    : QAlgorithms.Papers.Independent.Next46.P21.rectangle_thresholds_sharp
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:37:18.827991+00:00
-- url     : https://prove2.me/theorems/9d3289f4-2ee8-4b68-a4f0-9f8c6264d4d0
-- title:
--   Explicit sharpness rectangles
-- statement:
--   For real intervals $I,J$, let $F(I,J)=\{\alpha\in\mathbb Z[\sqrt2]:\alpha\in I,\ \alpha^\bullet\in J\}$, where $\bullet$ sends $\sqrt2$ to $-\sqrt2$. Then
--
--   $$
--   F([0,1],[0,1])=\{0,1\},
--   $$
--   $$
--   F([0,1+\sqrt2],[-\sqrt2,1])=\{0,1,\sqrt2,1+\sqrt2\}.
--   $$
--
--   For every real $\eta>0$,
--
--   $$
--   F([\eta,1+\sqrt2-\eta],[-\sqrt2+\eta,1-\eta])=\varnothing.
--   $$
--
--   The last assertion also includes empty inward-shrunken intervals. These witnesses establish the sharpness of the uniqueness and covering thresholds.
-- source:
--   Efficient Clifford+T approximation of single-qubit operators, arXiv:1212.6253v2, PDF p. 8, Remark 18: sharpness of the rectangle thresholds

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P21

open Set

open scoped ComplexConjugate

/-- Remark 18, PDF p.8: the two explicit sharpness rectangles and their inward shrinkings. -/
theorem rectangle_thresholds_sharp :
    rectangleSolutions 0 1 0 1 = {0, 1} ∧
    rectangleSolutions 0 (1 + Real.sqrt 2) (-Real.sqrt 2) 1 =
      {0, 1, (⟨0, 1⟩ : Zsqrtd 2), (⟨1, 1⟩ : Zsqrtd 2)} ∧
    ∀ eta : ℝ, 0 < eta →
      rectangleSolutions eta (1 + Real.sqrt 2 - eta) (-Real.sqrt 2 + eta) (1 - eta) = ∅ := by sorry

end QAlgorithms.Papers.Independent.Next46.P21

end
