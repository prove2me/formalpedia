-- Prove2me | Theorems.Thm_SoftmaxAttnFD_lemma_4_3
-- name    : SoftmaxAttnFD.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:01:38.845202+00:00
-- url     : https://prove2.me/theorems/e4ff0cc5-630a-4a42-a3af-f7c1b3c30792
-- title:
--   Lemma 4.3, p.15 — centroid bound in the plane
-- statement:
--   Let $C=\mathrm{conv}\{k_1,\dots,k_n\}\subset\mathbb R^2$ have positive area and area centroid at the origin. For $q\in\mathbb R^2\setminus\{0\}$, let $h=\max_{x\in C}q\cdot x$ and $h_-=\min_{x\in C}q\cdot x$. Then
--   $$h>0\quad\text{and}\quad h_-\ge-2h.$$
--   So in a centered polygon all scores in a row lie within $3h$ of the maximum, which bounds the score range for rows with small maximum.
--
--   Differences from the source:
--   - generalization: the rounded, centered keys of §4.2, which are rational → any real keys whose hull has positive area and area centroid 0; reason: the lemma uses only those properties; the page's polygon is an instance
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Lemma 4.3 and §4.2, p.15

import Mathlib

open MeasureTheory

namespace SoftmaxAttnFD

/-- **Lemma 4.3** (arXiv:2611.06055, sha256 a60f7609…, p.15). The centered polygon `C` (§4.2, p.15) is
the convex hull of finitely many keys, has positive area, and has its area centroid at the origin.
For `q ≠ 0`, with `h = max_{x∈C} q·x` and `h₋ = min_{x∈C} q·x`, we have `h > 0` and `h₋ ≥ −2h`.

**Formalization Note** Positive area is `(interior C).Nonempty`; the centroid is Bochner over Lebesgue
measure on a compact set, so it is integrable and the condition is not a junk value. -/
theorem lemma_4_3 (n : ℕ) (k : Fin n → Fin 2 → ℝ) (C : Set (Fin 2 → ℝ))
    (hC : C = convexHull ℝ (Set.range k)) (harea : (interior C).Nonempty)
    (hcentroid : ∫ x in C, x ∂volume = 0) (q : Fin 2 → ℝ) (hq : q ≠ 0) (h hm : ℝ)
    (hh : IsGreatest ((fun x => q ⬝ᵥ x) '' C) h) (hhm : IsLeast ((fun x => q ⬝ᵥ x) '' C) hm) :
    0 < h ∧ -2 * h ≤ hm := by sorry

end SoftmaxAttnFD
