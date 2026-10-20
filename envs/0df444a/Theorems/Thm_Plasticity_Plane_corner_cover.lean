-- Prove2me | Theorems.Thm_Plasticity_Plane_corner_cover
-- name    : Plasticity.Plane.corner_cover
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:27.810264+00:00
-- url     : https://prove2.me/theorems/1af69a8b-13bf-4f47-92ce-33223739d09f
-- title:
--   The corner cover: at a corner of a planar ball, two short translates along its edges cover the ball outside any neighbourhood of the corner
-- statement:
--   Let $V$ be a real normed space of dimension $2$ with closed unit ball $D$.
--   Let $x,x_1\in D$ and $x_2\in V$, and let $f_1,f_2$ be functionals of norm $1$ with $f_1(x_1)=f_1(x)=1$, $f_2(x)=f_2(x_2)=1$, $f_1(x_2)<1$ and $f_2(x_1)<1$; the point $x_2$ need not lie in $D$.
--   Then for every neighbourhood $U$ of $x$ there is $r>0$ such that $$D\subseteq U\cup\bigl(-\mu(x-x_1)+D\bigr)\cup\bigl(\mu'(x_2-x)+D\bigr)\qquad(0<\mu\le r,\ 0<\mu'\le r),$$ where $c+D$ is the closed unit ball about $c$.
--   When also $x_2\in D$, the hypotheses say that $x$ is a common endpoint of the segments $[x_1,x]$ and $[x,x_2]$, which lie in two different faces of $D$, those where $f_1=1$ and where $f_2=1$.
-- source:
--   This repository: claim CUB102(3) (claims/cub.md), proof in expositions/c0_planes_front.md §2.3

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.Plane
theorem corner_cover {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (x x₁ x₂ : V) (f₁ f₂ : StrongDual ℝ V)
    (hf₁ : ‖f₁‖ = 1) (hf₂ : ‖f₂‖ = 1) (hx₁ : ‖x₁‖ ≤ 1) (hx : ‖x‖ ≤ 1)
    (h₁x₁ : f₁ x₁ = 1) (h₁x : f₁ x = 1) (h₂x : f₂ x = 1) (h₂x₂ : f₂ x₂ = 1)
    (h₁x₂ : f₁ x₂ < 1) (h₂x₁ : f₂ x₁ < 1) (U : Set V) (hU : U ∈ nhds x) :
    ∃ r > 0, ∀ μ μ' : ℝ, 0 < μ → μ ≤ r → 0 < μ' → μ' ≤ r →
      Metric.closedBall (0 : V) 1 ⊆
        U ∪ Metric.closedBall (-(μ • (x - x₁))) 1 ∪ Metric.closedBall (μ' • (x₂ - x)) 1 := by sorry
end Plasticity.Plane
