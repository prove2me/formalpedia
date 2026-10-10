-- Prove2me | Theorems.Thm_StrictCQ_CAKKT_lemma_6_1
-- name    : StrictCQ.CAKKT.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:22.422234+00:00
-- url     : https://prove2.me/theorems/f248480b-afa1-41de-8c2e-3e25fce5bcb0
-- title:
--   Lemma 6.1, p. 22 — every y ∈ T_Ω(x̄)° is −∇F(x̄) for a C¹ function F with strict global minimum over Ω at x̄
-- statement:
--   Let $\Omega$ be the feasible set of a system of continuously differentiable constraints $h_i(x)=0$, $g_j(x)\le 0$, and let $\bar x\in\Omega$. For every $y$ in the polar $T_\Omega(\bar x)^\circ$ of the tangent cone there is a continuously differentiable $F:\mathbb R^n\to\mathbb R$ with
--   $$-\nabla F(\bar x)=y\qquad\text{and}\qquad F(\bar x)<F(x)\ \text{ for all } x\in\Omega,\ x\neq\bar x.$$
--
--   This is Rockafellar–Wets, *Variational Analysis*, Theorem 6.11, specialized to $\Omega$. It realizes every polar tangent vector as the negative gradient of an objective minimized exactly at $\bar x$, which is how geometric normals are turned into optimization problems in Lemma 6.2.
--
--   **Formalization Note** "Smooth" is read as $C^1$ (`ContDiff ℝ 1`), as in Rockafellar–Wets. The $C^1$ hypothesis on $h,g$ is the paper's standing assumption.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 22, Lemma 6.1 (citing Rockafellar–Wets, Theorem 6.11)

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.CAKKT

theorem lemma_6_1 {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    {xbar y : EuclideanSpace ℝ (Fin n)} (hxbar : xbar ∈ C.feasible)
    (hy : y ∈ StrictCQ.AGP.polar (tangentCone C.feasible xbar)) :
    ∃ F : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 F ∧ -gradient F xbar = y ∧
      ∀ x ∈ C.feasible, x ≠ xbar → F xbar < F x := by sorry
end StrictCQ.CAKKT
