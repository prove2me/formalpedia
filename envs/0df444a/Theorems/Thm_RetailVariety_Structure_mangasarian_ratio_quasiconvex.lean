-- Prove2me | Theorems.Thm_RetailVariety_Structure_mangasarian_ratio_quasiconvex
-- name    : RetailVariety.Structure.mangasarian_ratio_quasiconvex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:20.411359+00:00
-- url     : https://prove2.me/theorems/feed2e54-3c0e-421b-a4a3-4f65d35f4e8e
-- title:
--   Mangasarian (1969): a convex function over a positive affine function is quasiconvex
-- statement:
--   Let $X$ be a convex subset of a real vector space, let $g$ be convex on $X$, and let $f$ be affine ("linear") on $X$ with $f(x)>0$ for all $x\in X$. Then the ratio
--   $$x\mapsto\frac{g(x)}{f(x)}$$
--   is quasiconvex on $X$: each of its sublevel sets $\{x\in X: g(x)/f(x)\le r\}$ is convex.
--
--   The paper quotes this result from Mangasarian, *Nonlinear Programming* (1969), and applies it with $X=[0,v_1]$, $f$ of (9) and $g=g_I,g_T$ of (10)–(11) to prove Lemma 1.
--
--   **Formalization Note** "$f$ is linear on $X$" is encoded as: $f$ is both convex and concave on $X$.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1507, Appendix, proof of Lemma 1 (result quoted from Mangasarian 1969)

import Mathlib

namespace RetailVariety.Structure

/-- Mangasarian (1969), as quoted in the proof of Lemma 1 (Appendix, p. 1507): if `g` is convex
on the convex set `X`, `f > 0` on `X`, and `f` is linear (affine) on `X`, then `g / f` is
quasiconvex on `X`. "Affine on `X`" is encoded as convex and concave on `X`. -/
theorem mangasarian_ratio_quasiconvex {E : Type*} [AddCommGroup E] [Module ℝ E] (X : Set E)
    (g f : E → ℝ) (hg : ConvexOn ℝ X g) (hf_pos : ∀ x ∈ X, 0 < f x)
    (hf_lin : ConvexOn ℝ X f ∧ ConcaveOn ℝ X f) :
    QuasiconvexOn ℝ X (fun x => g x / f x) := by sorry

end RetailVariety.Structure
