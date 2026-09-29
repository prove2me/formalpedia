-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_normalized_factor_degree_le
-- name    : PachDeZeeuw.Algebraic.normalized_factor_degree_le
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:21.839764+00:00
-- url     : https://prove2.me/theorems/8fd9e5b0-ad6f-4106-8eef-9a75ad394c51
-- title:
--   Normalized factor $h$ of $p$ satisfies totalDegree bound
-- statement:
--   Let $p$ and $h$ be bivariate real polynomials with $h_{p0} : p \neq 0$, and let $h_h$ witness that $h$ is one of the normalized factors of $p$ in the unique factorization monoid $\mathrm{MvPolynomial}\,(\mathrm{Fin}\,2)\,\mathbb{R}$. Then the total degree does not grow on passing to a factor:
--
--   $${h.\mathrm{totalDegree} \leq p.\mathrm{totalDegree}.}$$
--
--   The proof extracts $h \mid p$ from membership in the normalized factors and applies `MvPolynomial.totalDegree_le_of_dvd_of_isDomain`. This degree monotonicity lets the development pass global degree hypotheses on a reducible curve down to each irreducible factor, so that the per-pair bound of `irreducible_pair_intersection_bound`, namely $(d_1 + d_2 + 1)^4$, applies to every factor pair and can be summed in `factorized_bezout_bound`; it is used the same way in `factor_intersection_bound`.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1498-L1504

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.normalized_factor_degree_le {p h : MvPolynomial (Fin 2) ℝ} (hp0 : p ≠ 0)
    (hh : h ∈ UniqueFactorizationMonoid.normalizedFactors p) :
    h.totalDegree ≤ p.totalDegree := by sorry
