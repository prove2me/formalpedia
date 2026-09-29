-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_nonsingular_point_has_infinite_zeroSet_of_partial0
-- name    : PachDeZeeuw.Algebraic.nonsingular_point_has_infinite_zeroSet_of_partial0
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:45.110524+00:00
-- url     : https://prove2.me/theorems/5b8286f9-0403-412d-90b7-bd0f24d7213f
-- title:
--   Nonsingular point with $\partial_0 h(z) \neq 0$ forces infinite zero set
-- statement:
--   Let $h$ be a plane polynomial ($h : \mathrm{PlanePoly}$), $z$ a point of the plane with $h_z : z \in \mathrm{PlaneCurveZeroSet}\,h$, and suppose the partial derivative in the first variable does not vanish at $z$:
--
--   $$\mathrm{eval}\,(i \mapsto z\,i)\,(\partial_0 h) \neq 0.$$
--
--   Then the zero set of $h$ is infinite:
--
--   $${(\mathrm{PlaneCurveZeroSet}\,h).\mathrm{Infinite}.}$$
--
--   This is one of the two nonsingularity-implies-infinite-curve lemmas (here for $\partial_0$). The underlying tool is the smooth ($C^\infty$, `ContDiff`) implicit function theorem, invoked through `ContDiffAt.implicitFunction`: a point where a partial derivative is nonzero lies on a locally graphed segment of the curve, so the curve is infinite. The $\partial_0$ case is obtained from the $\partial_1$ case by renaming the two variables of $h$ with the swap and moving points with $\mathrm{swapPoint}$. It supports the fact that a finite real zero set consists entirely of singular points, which is needed to count singularities of irreducible curves.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L666-L728

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.nonsingular_point_has_infinite_zeroSet_of_partial0 (h : PlanePoly) {z : Point2}
    (hz : z ∈ PlaneCurveZeroSet h)
    (hnonsing :
      MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (0 : Fin 2) h) ≠ 0) :
    (PlaneCurveZeroSet h).Infinite := by sorry
