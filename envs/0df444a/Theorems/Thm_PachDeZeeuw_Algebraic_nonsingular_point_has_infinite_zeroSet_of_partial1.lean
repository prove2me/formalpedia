-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_nonsingular_point_has_infinite_zeroSet_of_partial1
-- name    : PachDeZeeuw.Algebraic.nonsingular_point_has_infinite_zeroSet_of_partial1
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:08.686443+00:00
-- url     : https://prove2.me/theorems/b68bfd7e-f3a9-4dcb-a161-dee89d363910
-- title:
--   Nonsingular point with $\partial_1 h(z) \neq 0$ forces infinite zero set
-- statement:
--   Let $h$ be a plane polynomial ($h : \mathrm{PlanePoly}$), $z$ a point of the plane with $h_z : z \in \mathrm{PlaneCurveZeroSet}\,h$, and suppose the partial derivative in the second variable does not vanish at $z$:
--
--   $$\mathrm{eval}\,(i \mapsto z\,i)\,(\partial_1 h) \neq 0.$$
--
--   Then the zero set of $h$ is infinite:
--
--   $${(\mathrm{PlaneCurveZeroSet}\,h).\mathrm{Infinite}.}$$
--
--   This is the companion of the $\partial_0$ version, covering nonsingularity detected in the second coordinate. Together the two lemmas show that any finite real algebraic curve has both partials vanishing at every one of its points, i.e. every point is singular; this feeds the singularity-counting bound for irreducible curves used in the Bezout argument.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L544-L664

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.nonsingular_point_has_infinite_zeroSet_of_partial1 (h : PlanePoly) {z : Point2}
    (hz : z ∈ PlaneCurveZeroSet h)
    (hnonsing :
      MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) h) ≠ 0) :
    (PlaneCurveZeroSet h).Infinite := by sorry
