-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_mem_PlaneCurveZeroSet
-- name    : PachDeZeeuw.Algebraic.mem_PlaneCurveZeroSet
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:34.535054+00:00
-- url     : https://prove2.me/theorems/77dea046-75fd-416b-b8cb-9d979595b014
-- title:
--   Membership in $\mathrm{PlaneCurveZeroSet}\,p$ holds exactly when $p$ evaluates to zero at $x$
-- statement:
--   Let $p$ be a bivariate real polynomial in $\mathrm{MvPolynomial}\,(\mathrm{Fin}\,2)\,\mathbb{R}$ and $x$ a point of the Euclidean plane $\mathrm{Point2}$. Then membership $x \in \mathrm{PlaneCurveZeroSet}\,p$ holds exactly when the evaluation vanishes,
--
--   $$\mathrm{eval}\,(i \mapsto x\,i)\,p = 0,$$
--
--   and the two conditions coincide by definitional unfolding (`Iff.rfl`): $\mathrm{PlaneCurveZeroSet}\,p$ is defined as the set of points at which $p$ evaluates to zero.
--
--   This is the basic membership unfolding lemma for plane curves: it converts the geometric statement "$x$ lies on the curve cut out by $p$" into the algebraic equation $p(x) = 0$. It is used throughout the preliminaries whenever a set-theoretic fact about zero sets must be reduced to polynomial arithmetic.
-- source:
--   Lean bridge lemma (definitional unfolding or coordinate bookkeeping) for the formalization of Pach–de Zeeuw, arXiv:1308.0177, Theorem 2.1; not a literature statement; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L121-L124

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

@[simp]
theorem PachDeZeeuw.Algebraic.mem_PlaneCurveZeroSet {p : MvPolynomial (Fin 2) ℝ}
    {x : Point2} :
    x ∈ PlaneCurveZeroSet p ↔ MvPolynomial.eval (fun i => x i) p = 0 := by sorry
