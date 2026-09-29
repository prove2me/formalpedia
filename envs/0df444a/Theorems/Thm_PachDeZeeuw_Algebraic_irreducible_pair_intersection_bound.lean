-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_irreducible_pair_intersection_bound
-- name    : PachDeZeeuw.Algebraic.irreducible_pair_intersection_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:37:53.908002+00:00
-- url     : https://prove2.me/theorems/47a14d0f-379b-45c5-9559-c930b39d4578
-- title:
--   Intersection bound for a pair of nonassociated irreducible curves
-- statement:
--   Let $h$ and $k$ be irreducible bivariate real polynomials ($h_h$, $h_k$) of total degrees at most $d_1$ and $d_2$, not associated to each other ($h_{\mathrm{not}} : \neg\,\mathrm{Associated}\,h\,k$). Then their real zero sets meet in a finite set, with an explicit bound:
--
--   $$(Z(h) \cap Z(k)).\mathrm{Finite} \;\land\; |Z(h) \cap Z(k)| \le (d_1 + d_2 + 1)^4.$$
--
--   The proof is a three-way case split on whether the curried polynomials $\mathrm{Curry0}\,h$ and $\mathrm{Curry0}\,k$ have degree zero in the eliminated variable. Both zero: the intersection is empty (`zeroCurry_zeroCurry_pair_intersection_bound`). Exactly one zero: `zeroCurry_nonvertical_pair_intersection_bound`, applied with the roles of $h$ and $k$ chosen so that the degree-zero one comes first, gives $d_1 d_2$. Both positive: the curries are primitive and relatively prime, and `primitive_nonvertical_pair_intersection_bound` gives $((d_1 + d_2)^2 + 1) \cdot \max(d_1, d_2)$. Each of these is at most $(d_1 + d_2 + 1)^4$. The associated case, a shared irreducible factor, is excluded here by hypothesis; in `factorized_bezout_bound` that case is handled separately through `finite_real_zero_set_of_irreducible_factor_bound` and the singularity count, since the hypothesis there only forbids a shared factor with infinite real zero set.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L370-L440

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.irreducible_pair_intersection_bound {d₁ : ℕ} {d₂ : ℕ} (h k : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h) (hk : Irreducible k)
    (hdeg : h.totalDegree ≤ d₁)
    (kdeg : k.totalDegree ≤ d₂)
    (hnot : ¬ Associated h k) :
    (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
        (d₁ + d₂ + 1) ^ 4 := by sorry
