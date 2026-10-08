-- Prove2me | Theorems.Thm_RetailVariety_Fashion_lemma_2
-- name    : RetailVariety.Fashion.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:48.425225+00:00
-- url     : https://prove2.me/theorems/a76477f1-8375-4953-b6e1-9949607c2993
-- title:
--   Lemma 2 (Karamata) — $x\prec y$ implies $\sum g(x_i)\le\sum g(y_i)$ for convex $g$
-- statement:
--   Let $s\subseteq\mathbb R$ be a convex set (an interval), $g:\mathbb R\to\mathbb R$ convex on $s$, and $x,y\in\mathbb R^n$ with every coordinate of $x$ and of $y$ in $s$. If $x\prec y$ (Definition 1), then
--   $$\sum_{i=1}^{n}g(x_i)\le\sum_{i=1}^{n}g(y_i).$$
--
--   This is the classical inequality of Hardy, Littlewood and Pólya (Karamata's inequality), which the paper quotes from Marshall and Olkin (1979). It is the step that turns majorization of preference vectors into a comparison of profits.
--
--   **Formalization Note.** The paper states the lemma for $g$ convex on all of $\mathbb R$, which is the case $s=\mathbb R$. The proof of Theorem 3 applies it to $g(x)=ax-bx^\beta$, which is convex (and defined as a real power) only on $[0,\infty)$, so the lemma is stated for $g$ convex on a convex set containing the data.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1505, Lemma 2 (citing Marshall and Olkin 1979)

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Majorization

namespace RetailVariety.Fashion

/-- Lemma 2 (van Ryzin & Mahajan 1999, p. 1505; Hardy–Littlewood–Pólya / Karamata, quoted from
Marshall & Olkin 1979), for `g` convex on a convex set `s` containing every coordinate of `x` and
`y`; the paper's `g : ℝ → ℝ` convex is the case `s = univ`. -/
theorem lemma_2 {n : ℕ} {s : Set ℝ} {g : ℝ → ℝ} (hg : ConvexOn ℝ s g)
    (x y : Fin n → ℝ) (hxs : ∀ i, x i ∈ s) (hys : ∀ i, y i ∈ s) (hxy : Majorized x y) :
    ∑ i, g (x i) ≤ ∑ i, g (y i) := by sorry

end RetailVariety.Fashion
