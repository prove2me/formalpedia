-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_zeroCurry_zeroCurry_pair_intersection_bound
-- name    : PachDeZeeuw.Algebraic.zeroCurry_zeroCurry_pair_intersection_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:08.978638+00:00
-- url     : https://prove2.me/theorems/e8762277-ea28-4831-8352-9d2081d49873
-- title:
--   Both-vertical non-associated pair has intersection below any bound
-- statement:
--   Let $h$ and $k$ be irreducible bivariate real polynomials ($h_h$, $h_k$) that are not associated ($h_{not}$), and suppose both are vertical: $h_{deg0} : (\mathrm{Curry0}\,h).\mathrm{natDegree} = 0$ and $k_{deg0} : (\mathrm{Curry0}\,k).\mathrm{natDegree} = 0$. Then for every natural number $B$ (an arbitrary bound parameter) the intersection is finite and bounded by $B$:
--
--   $${(\mathrm{PlaneCurveZeroSet}\,h \cap \mathrm{PlaneCurveZeroSet}\,k).\mathrm{Finite} \land (\mathrm{PlaneCurveZeroSet}\,h \cap \mathrm{PlaneCurveZeroSet}\,k).\mathrm{ncard} \leq B.}$$
--
--   Since each curve is a union of vertical lines and the two line families are disjoint (a shared line would make the irreducibles associated), the intersection is actually empty, hence below any $B$. This vacuous-but-uniform case closes the both-vertical branch of the irreducible pair-intersection case split with a bound that composes with the other branches.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1305-L1318

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.zeroCurry_zeroCurry_pair_intersection_bound (h k : MvPolynomial (Fin 2) ℝ)
    {B : ℕ}
    (hh : Irreducible h) (hk : Irreducible k)
    (hnot : ¬ Associated h k)
    (hdeg0 : (Curry0 h).natDegree = 0)
    (kdeg0 : (Curry0 k).natDegree = 0) :
    (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ B := by sorry
