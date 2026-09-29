-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_primitive_nonvertical_pair_intersection_bound
-- name    : PachDeZeeuw.Algebraic.primitive_nonvertical_pair_intersection_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:45.158341+00:00
-- url     : https://prove2.me/theorems/b593321f-2628-4168-a5bf-89aedec22de5
-- title:
--   Primitive nonvertical coprime pair has finite explicitly bounded intersection
-- statement:
--   Let $p$ and $q$ be bivariate real polynomials of total degree at most $d_1$ and $d_2$ respectively ($h_{pdeg}$, $h_{qdeg}$), with primitive curries ($h_{pprim}$, $h_{qprim}$), both genuinely depending on the first variable ($h_{p0deg} : 0 < (\mathrm{Curry0}\,p).\mathrm{natDegree}$, $h_{q0deg}$ likewise), and coprime curries ($h_{rel} : \mathrm{IsRelPrime}\,(\mathrm{Curry0}\,p)\,(\mathrm{Curry0}\,q)$). Then their common zero set is finite with an explicit bound:
--
--   $${(\mathrm{PlaneCurveZeroSet}\,p \cap \mathrm{PlaneCurveZeroSet}\,q).\mathrm{Finite} \land (\mathrm{PlaneCurveZeroSet}\,p \cap \mathrm{PlaneCurveZeroSet}\,q).\mathrm{ncard} \leq ((d_1 + d_2)^2 + 1) \cdot \max\,d_1\,d_2.}$$
--
--   This is the workhorse resultant-based intersection estimate of the preliminaries: the resultant in the coefficient variable has degree at most $(d_1+d_2)^2$, its roots index the nonempty fibers, and each fiber has at most $\max d_1 d_2$ points. Summing over components upgrades it to the finite Bezout bound for arbitrary (reducible) curves.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L225-L368

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.primitive_nonvertical_pair_intersection_bound (p q : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂)
    (hpprim : (Curry0 p).IsPrimitive)
    (hqprim : (Curry0 q).IsPrimitive)
    (hp0deg : 0 < (Curry0 p).natDegree)
    (hq0deg : 0 < (Curry0 q).natDegree)
    (hrel : IsRelPrime (Curry0 p) (Curry0 q)) :
    (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).Finite ∧
      (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
        ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂ := by sorry
