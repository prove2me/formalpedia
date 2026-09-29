-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_factor_intersection_bound
-- name    : PachDeZeeuw.Algebraic.factor_intersection_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:37:50.449727+00:00
-- url     : https://prove2.me/theorems/2bde73ec-33a7-4851-be2f-5e7e3da2cfae
-- title:
--   Intersection bound for an irreducible curve with a partial-derivative factor
-- statement:
--   Let $h$ be an irreducible plane polynomial ($h_h$) of total degree at most $d$, with a nonzero partial derivative $h_{pi} : \mathrm{pderiv}\,i\,h \ne 0$ for some $i : \mathrm{Fin}\,2$, and let $k$ be a normalized factor of that partial derivative ($h_k : k \in \mathrm{normalizedFactors}\,(\mathrm{pderiv}\,i\,h)$) that is not associated to $h$ ($h_{\mathrm{not}} : \neg\,\mathrm{Associated}\,h\,k$). Then the intersection of the two real zero sets is finite with an explicit bound:
--
--   $$(Z(h) \cap Z(k)).\mathrm{Finite} \;\land\; |Z(h) \cap Z(k)| \le (d+1)^4.$$
--
--   The factor $k$ is irreducible with total degree at most $d$ (via `normalized_factor_degree_le` and `totalDegree_pderiv_le`), and the proof is the same three-way case split as in `irreducible_pair_intersection_bound`: both curries of degree zero (empty intersection), exactly one of degree zero (bound $d \cdot d$), or both positive (primitive coprime curries, bound $((d+d)^2+1) \cdot d$); each is at most $(d+1)^4$. The associated case is excluded by $h_{\mathrm{not}}$, which `partial_factor_not_associated` supplies in the application. Every singular point of $h$ lies in at least one such intersection $Z(h) \cap Z(k)$ (`singularPointSet_subset_partial_factor_union`), so this lemma is the per-factor input to the finiteness and bound for the singular locus in `finite_singularities_of_irreducible_bound`.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L1032-L1088

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.factor_intersection_bound {d : ℕ} (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0)
    {k : PlanePoly}
    (hk : k ∈ UniqueFactorizationMonoid.normalizedFactors (MvPolynomial.pderiv i h))
    (hnot : ¬ Associated h k) :
    (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ (d + 1) ^ 4 := by sorry
