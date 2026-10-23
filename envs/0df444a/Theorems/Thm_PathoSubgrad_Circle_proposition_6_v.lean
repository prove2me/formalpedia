-- Prove2me | Theorems.Thm_PathoSubgrad_Circle_proposition_6_v
-- name    : PathoSubgrad.Circle.proposition_6_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:34.744974+00:00
-- url     : https://prove2.me/theorems/64b99beb-561f-4558-a166-33a5d97e7a8b
-- title:
--   Proposition 6 (v), p. 7 — f is Lipschitz and path-differentiable
-- statement:
--   Let $\psi$ be any bump profile, $i_0\ge2$, and $f$ the function (4) of the example on the circle. Then $f$ is (globally) Lipschitz, and $f$ is path-differentiable: for every Lipschitz curve $\gamma:\mathbb R\to\mathbb R^2$ and almost every $t$,
--   $$(f\circ\gamma)'(t)=v\cdot\gamma'(t)\qquad\text{for all } v\in\partial^c f(\gamma(t)).$$
--
--   Path differentiability is the regularity class in which the paper's companion work proves its positive results on the subgradient method; the example shows these results cannot be upgraded to convergence.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, p. 7, Proposition 6 (v)

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_PathoSubgrad_Circle_Construction

open Filter Topology
open scoped InnerProductSpace ContDiff

namespace PathoSubgrad.Circle

theorem proposition_6_v (Ψ : BumpProfile) (i0 : ℕ) (hi0 : 2 ≤ i0) :
    (∃ K, LipschitzWith K (fCirc Ψ i0)) ∧ IsPathDifferentiable (fCirc Ψ i0) := by sorry

end PathoSubgrad.Circle
