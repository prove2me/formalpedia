-- Prove2me | Theorems.Thm_ToddKK14_Diameter_base_dim_one
-- name    : ToddKK14.Diameter.base_dim_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:45:51.526394+00:00
-- url     : https://prove2.me/theorems/91330b8d-25f7-4cba-aa40-fde403fbfc52
-- title:
--   §2, p. 3, proof of Theorem 1 — d = 1: every polyhedron on the line has diameter at most 1
-- statement:
--   Let $P=\{x\in\mathbb R : a_i x\le b_i,\ i=1,\dots,n\}$ be any polyhedron on the real line cut out by $n$ linear inequalities, bounded or not. Then any two vertices of $P$ are equal or adjacent:
--
--   $$
--   \delta(P)\le 1, \qquad\text{so}\qquad \Delta(1,n)\le 1 .
--   $$
--
--   A polyhedron on the line is empty, a point, a half-line, a segment or the whole line; it has at most two vertices, and when it has two it is the segment between them, which is an edge. This is the case $d=1$ of the induction in the proof of Theorem 1, where the bound $(n-1)^{\log 1}=1$ is "the correct value".
--
--   **Formalization Note** The statement uses the inequality reading of $\Delta(1,n)\le 1$ (every `Hpoly a b` in $\mathbb R^1$ with $n$ rows satisfies `DiamLE … 1`) and holds for every $n$; genuine $(1,n)$-polyhedra exist only for $n\le 2$. The value $\Delta(1,1)=0$ is the second clause of the goal theorem, not of this one. No boundedness or nonzero-row hypothesis is imposed.
-- source:
--   Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, arXiv:1402.3579v2, p. 3, §2, proof of Theorem 1, sentence "Next, the right-hand side gives 1 for d = 1 (n = 2) and n − 2 for d = 2" (d = 1 part)

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace ToddKK14.Diameter

open Hirsch

/-- Todd (2014), p. 3, proof of Theorem 1: "the right-hand side gives 1 for d = 1 (n = 2) … which
[is] the correct value". Every polyhedron on the line `ℝ¹` cut out by any number `n` of
inequalities, bounded or not, has graph diameter at most `1`. -/
theorem base_dim_one (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin 1)) (b : Fin n → ℝ) :
    DiamLE (Hpoly a b) 1 := by sorry

end ToddKK14.Diameter
