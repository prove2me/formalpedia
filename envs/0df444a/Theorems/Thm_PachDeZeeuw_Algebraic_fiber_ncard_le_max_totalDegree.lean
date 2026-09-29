-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_fiber_ncard_le_max_totalDegree
-- name    : PachDeZeeuw.Algebraic.fiber_ncard_le_max_totalDegree
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:37:59.251765+00:00
-- url     : https://prove2.me/theorems/4a978f61-4781-4a11-be58-edfe1c8b58ff
-- title:
--   Common-zero fiber bounded by the maximum total degree
-- statement:
--   Let $p$ and $q$ be bivariate real polynomials and $x \in \mathbb{R}$ a coefficient value such that at least one specialization is nonzero ($\mathrm{Specialized}_0(x,p) \ne 0 \lor \mathrm{Specialized}_0(x,q) \ne 0$). Then the set of common zeros in the fiber over $x$ satisfies
--
--   $$|\mathrm{FiberCommonZeros}(x, p, q)| \le \max(p.\mathrm{totalDegree},\, q.\mathrm{totalDegree}).$$
--
--   Since a nonzero specialization has degree at most the total degree, its root set (hence any common-zero subset) is bounded accordingly. Summing this per-fiber estimate over the finitely many bad fibers gives the global intersection bounds.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L556-L611

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.fiber_ncard_le_max_totalDegree (p q : MvPolynomial (Fin 2) ℝ) (x : ℝ)
    (h : Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0) :
    (FiberCommonZeros x p q).ncard ≤ max p.totalDegree q.totalDegree := by sorry
