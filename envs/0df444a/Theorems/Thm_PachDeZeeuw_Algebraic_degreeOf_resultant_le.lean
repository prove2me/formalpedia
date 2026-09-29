-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_degreeOf_resultant_le
-- name    : PachDeZeeuw.Algebraic.degreeOf_resultant_le
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:37:39.574951+00:00
-- url     : https://prove2.me/theorems/40449529-80d7-4a48-b40c-9943ba595a45
-- title:
--   Degree bound $(d_1+d_2)^2$ on the coefficient resultant
-- statement:
--   Let $p$ and $q$ be bivariate real polynomials of total degrees bounded by $d_1$ and $d_2$ respectively ($p.\mathrm{totalDegree} \le d_1$, $q.\mathrm{totalDegree} \le d_2$). Then the coefficient-degree of their coefficient resultant satisfies
--
--   $$\mathrm{degreeOf}_0(\mathrm{ResultantCoeff}(p, q)) \le (d_1 + d_2)^2.$$
--
--   Here $\mathrm{ResultantCoeff}(p,q)$ is the resultant of the curried polynomials over the coefficient ring. Bounding its degree bounds the number of its roots, hence the number of bad fibers over which the two specializations can share a root; this is the quantitative heart of the resultant-based intersection bound.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L127-L206

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.degreeOf_resultant_le (p q : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂) :
    MvPolynomial.degreeOf (0 : Fin 1) (ResultantCoeff p q) ≤ (d₁ + d₂) ^ 2 := by sorry
