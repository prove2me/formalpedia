-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_finite_singularities_of_irreducible_bound
-- name    : PachDeZeeuw.Algebraic.finite_singularities_of_irreducible_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:11.526367+00:00
-- url     : https://prove2.me/theorems/519dbe7d-b4fe-41ac-9fab-26420a87f16f
-- title:
--   Finite singularity bound for an irreducible plane curve
-- statement:
--   Let $h$ be an irreducible plane polynomial of total degree at most $d$ with a nonzero partial derivative $\mathrm{pderiv}_i(h) \ne 0$. Then its singular locus (common zeros of $h$ and both partials) is finite with an explicit bound:
--
--   $$|\mathrm{SingularPointSet}(h)| \le (d+1)^5.$$
--
--   The proof covers the singular set by intersections of $h$ with factors of the nonzero partial and applies the factor-intersection bound. Finiteness of singularities is needed in the Pach--de Zeeuw incidence argument to discard a controlled bad set and work on the smooth part of the curve.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L1090-L1159

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.finite_singularities_of_irreducible_bound {d : ℕ} (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0) :
    (SingularPointSet h).Finite ∧
      (SingularPointSet h).ncard ≤ (d + 1) ^ 5 := by sorry
