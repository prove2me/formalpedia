-- Prove2me | Theorems.Thm_PathoSubgrad_Circle_lemma_7_eq6
-- name    : PathoSubgrad.Circle.lemma_7_eq6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:37.014319+00:00
-- url     : https://prove2.me/theorems/3a7e5aef-3191-4e22-8f85-eb5ea8bf4466
-- title:
--   Lemma 7, (6), p. 7 — for i large enough, dist(x_i, y) ≤ 2^{1−i} implies ‖x_i/‖x_i‖ − y/‖y‖‖ ≤ 3 dist(x_i, y)
-- statement:
--   Let $x_i$ be the points of the example on the circle. For $i$ large enough and every $y\in\mathbb R^2$ with $\operatorname{dist}(x_i,y)\le2^{1-i}$,
--   $$\Bigl\|\frac{x_i}{\|x_i\|}-\frac{y}{\|y\|}\Bigr\|\le3\operatorname{dist}(x_i,y).$$
--
--   Radial projection is $3$-Lipschitz on the small balls $B_{1/2^{i-1}}(x_i)$ that carry the bumps $\psi_i$; this lets the gradient estimates at $x_i$ be transported to the whole ball.
--
--   **Formalization Note.** "For $i$ large enough" is $\exists N,\ \forall i\ge N$, with $N$ independent of $y$. The junk value $\|0\|^{-1}=0$ never enters, since $\operatorname{dist}(x_i,0)=\|x_i\|>2^{1-i}$ for $i\ge2$.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, p. 7, Lemma 7, (6)

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_PathoSubgrad_Circle_Construction

open Filter Topology
open scoped InnerProductSpace ContDiff

namespace PathoSubgrad.Circle

theorem lemma_7_eq6 : ∃ N : ℕ, ∀ i ≥ N, ∀ y : EuclideanSpace ℝ (Fin 2),
    dist (xs i) y ≤ (2 : ℝ) ^ (1 - (i : ℤ)) →
    ‖‖xs i‖⁻¹ • xs i - ‖y‖⁻¹ • y‖ ≤ 3 * dist (xs i) y := by sorry

end PathoSubgrad.Circle
