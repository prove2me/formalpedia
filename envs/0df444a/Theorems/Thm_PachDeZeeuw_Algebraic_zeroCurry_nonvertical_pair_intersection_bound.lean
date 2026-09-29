-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_zeroCurry_nonvertical_pair_intersection_bound
-- name    : PachDeZeeuw.Algebraic.zeroCurry_nonvertical_pair_intersection_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:52.490595+00:00
-- url     : https://prove2.me/theorems/4a6ffd95-c4eb-404f-b950-79416cc2c949
-- title:
--   Vertical/nonvertical irreducible pair meets in at most $d_1 d_2$ points
-- statement:
--   Let $h$ and $k$ be irreducible bivariate real polynomials ($h_h$, $h_k$) that are not associated ($h_{not}$), of total degree at most $d_1$ and $d_2$ ($h_{deg}$, $k_{deg}$). Suppose $h$ is vertical, $h_{deg0} : (\mathrm{Curry0}\,h).\mathrm{natDegree} = 0$, while $k$ genuinely depends on the first variable, $k_{pos} : 0 < (\mathrm{Curry0}\,k).\mathrm{natDegree}$. Then the intersection is finite with the clean Bezout product bound:
--
--   $${(\mathrm{PlaneCurveZeroSet}\,h \cap \mathrm{PlaneCurveZeroSet}\,k).\mathrm{Finite} \land (\mathrm{PlaneCurveZeroSet}\,h \cap \mathrm{PlaneCurveZeroSet}\,k).\mathrm{ncard} \leq d_1 \cdot d_2.}$$
--
--   This handles the mixed vertical/nonvertical irreducible case: the vertical curve $h$ contributes at most $d_1$ lines, and on each line $k$ restricts to a nonzero univariate polynomial of degree at most $d_2$. It supplies the sharp $d_1 d_2$ estimate for this case in the case split assembling the full irreducible pair-intersection bound.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1240-L1268

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.zeroCurry_nonvertical_pair_intersection_bound (h k : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (hh : Irreducible h) (hk : Irreducible k)
    (hdeg : h.totalDegree ≤ d₁)
    (kdeg : k.totalDegree ≤ d₂)
    (hnot : ¬ Associated h k)
    (hdeg0 : (Curry0 h).natDegree = 0)
    (kpos : 0 < (Curry0 k).natDegree) :
    (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ d₁ * d₂ := by sorry
