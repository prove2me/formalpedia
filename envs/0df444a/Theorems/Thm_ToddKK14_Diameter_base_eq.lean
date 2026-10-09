-- Prove2me | Theorems.Thm_ToddKK14_Diameter_base_eq
-- name    : ToddKK14.Diameter.base_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:43.991892+00:00
-- url     : https://prove2.me/theorems/72a95ffe-1117-4916-bb82-c19806761d8c
-- title:
--   §2, p. 3, proof of Theorem 1 — ∆(d, d) = 0: a polyhedron with n = d has at most one vertex
-- statement:
--   Let $d\ge 0$ and let $P=\{x\in\mathbb R^d : \langle a_i,x\rangle\le b_i,\ i=1,\dots,d\}$ be any polyhedron cut out by exactly $d$ linear inequalities, bounded or not. Then any two vertices of $P$ are joined by a path of length $0$ in the vertex–edge graph of $P$; that is,
--
--   $$
--   \delta(P) = 0, \qquad\text{so}\qquad \Delta(d,d)=0 .
--   $$
--
--   Equivalently, $P$ has at most one vertex: a vertex needs $d$ linearly independent tight inequalities, and with only $d$ inequalities they determine the point. This is the base case $n=d$ of the induction in the proof of Theorem 1, and the equation $\Delta(d,d)=0$ is used again in the paper's check of the remaining small cases.
--
--   **Formalization Note** "$\Delta(d,d)\le 0$" is read as an inequality statement: every polyhedron `Hpoly a b` in $\mathbb R^d$ with $d$ rows satisfies `DiamLE (Hpoly a b) 0`. Vertices are extreme points. No boundedness, nonemptiness, full-dimensionality or nonzero-row hypothesis is imposed.
-- source:
--   Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, arXiv:1402.3579v2, p. 3, §2, proof of Theorem 1, sentence "The result is trivial for n = d"

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace ToddKK14.Diameter

open Hirsch

/-- Todd (2014), p. 3, proof of Theorem 1: "The result is trivial for n = d, since there can be only
one vertex." Every polyhedron in `ℝ^d` cut out by `d` inequalities, bounded or not, has graph
diameter `0`: ∆(d, d) = 0. -/
theorem base_eq (d : ℕ) (a : Fin d → EuclideanSpace ℝ (Fin d)) (b : Fin d → ℝ) :
    DiamLE (Hpoly a b) 0 := by sorry

end ToddKK14.Diameter
