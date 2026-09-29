-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_factorized_bezout_bound
-- name    : PachDeZeeuw.Algebraic.factorized_bezout_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:00.39692+00:00
-- url     : https://prove2.me/theorems/7abdefa2-e667-4a0a-b062-af61c2ee833e
-- title:
--   Factorized B\u00e9zout bound for curves with no common infinite factor
-- statement:
--   Let $p$ and $q$ be nonzero plane polynomials ($h_{p0} : p \neq 0$, $h_{q0} : q \neq 0$) of total degrees at most $d_1$ and $d_2$, and assume they share no common irreducible factor with infinite real zero set ($h_{\mathrm{noinf}} : \neg\,\mathrm{HasCommonInfiniteIrreducibleFactor}\,p\,q$). Then their real zero sets meet in a finite set, with an explicit bound:
--
--   $$(Z(p) \cap Z(q)).\mathrm{Finite} \;\land\; |Z(p) \cap Z(q)| \le (d_1 + d_2 + 1)^8.$$
--
--   The proof covers $Z(p) \cap Z(q)$ by the intersections $Z(h) \cap Z(k)$ over pairs $(h, k)$ of normalized factors of $p$ and $q$, and bounds each pair by $(d_1 + d_2 + 1)^5$ in one of two branches. If $h$ and $k$ are associated (a shared irreducible factor, which the hypothesis allows when its real zero set is finite), then $Z(h) = Z(k)$ and the bound comes from `finite_real_zero_set_of_irreducible_factor_bound`, that is, from the singularity count of $h$. If $h$ and $k$ are not associated, `irreducible_pair_intersection_bound` gives $(d_1 + d_2 + 1)^4$. The number of pairs is at most $d_1 d_2 \le (d_1 + d_2 + 1)^2$, which gives the eighth power. This lemma feeds directly into the existential `bezout` statement.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L1179-L1319

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.factorized_bezout_bound {d₁ : ℕ} {d₂ : ℕ} (p q : PlanePoly)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂)
    (hnoinf : ¬ HasCommonInfiniteIrreducibleFactor p q) :
    (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).Finite ∧
      (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
        (d₁ + d₂ + 1) ^ 8 := by sorry
