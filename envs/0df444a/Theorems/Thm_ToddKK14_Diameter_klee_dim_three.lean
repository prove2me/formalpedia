-- Prove2me | Theorems.Thm_ToddKK14_Diameter_klee_dim_three
-- name    : ToddKK14.Diameter.klee_dim_three
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:36.89005+00:00
-- url     : https://prove2.me/theorems/67ec8df8-7c35-4421-b099-ec4b2e0152e9
-- title:
--   §2, p. 3, proof of Theorem 1 — Klee: every 3-polyhedron with n facets, bounded or not, has diameter at most n − 3
-- statement:
--   Let $P=\{x\in\mathbb R^3 : \langle a_i,x\rangle\le b_i,\ i=1,\dots,n\}$ be any polyhedron in three-space cut out by $n$ linear inequalities, **bounded or not**. Then any two vertices of $P$ are joined by a path of at most $n-3$ edges:
--
--   $$
--   \delta(P)\le n-3, \qquad\text{so}\qquad \Delta(3,n)\le n-3 .
--   $$
--
--   This is the Hirsch bound in dimension three, established by Klee (V. Klee, *Diameters of polyhedral graphs*, Canad. J. Math. 16 (1964); *Paths on polyhedra I, II*, J. SIAM 13 (1965), Pacific J. Math. 17 (1966)), references [9, 10, 11] of the paper. Todd cites it as "the correct value $n-3$" and uses it as the base case $d=3$ of the induction proving Theorem 1, since $n-3\le (n-3)^{\log 3}$. The bounded case is already formalized; the induction needs the unbounded one.
--
--   **Formalization Note** Inequality reading: every `Hpoly a b` in $\mathbb R^3$ with $n$ rows satisfies `DiamLE … (n - 3)`, which includes connectivity of the graph. The subtraction $n-3$ is truncated at $0$ in $\mathbb N$; this is harmless, because for $n<3$ the polyhedron has no vertex (a vertex needs three linearly independent tight inequalities). No boundedness, nonemptiness, full-dimensionality or nonzero-row hypothesis is imposed.
-- source:
--   Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, arXiv:1402.3579v2, p. 3, §2, proof of Theorem 1, sentence "For d = 3, it gives (n − 3)^{log(3)}, which is greater than the correct value n − 3 established by Klee [9, 10, 11]"

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace ToddKK14.Diameter

open Hirsch

/-- Todd (2014), p. 3, proof of Theorem 1: "the correct value n − 3 established by Klee [9, 10, 11]".
Every polyhedron in `ℝ³` cut out by `n` inequalities, bounded or not, has graph diameter at most
`n − 3` (natural-number subtraction; for `n < 3` such a polyhedron has no vertex). -/
theorem klee_dim_three (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin 3)) (b : Fin n → ℝ) :
    DiamLE (Hpoly a b) (n - 3) := by sorry

end ToddKK14.Diameter
