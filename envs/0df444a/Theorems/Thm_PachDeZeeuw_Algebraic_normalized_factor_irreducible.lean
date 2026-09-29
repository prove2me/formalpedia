-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_normalized_factor_irreducible
-- name    : PachDeZeeuw.Algebraic.normalized_factor_irreducible
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:15.981806+00:00
-- url     : https://prove2.me/theorems/187115c0-7c42-4ce9-a7b8-1e6d9014dd10
-- title:
--   Every normalized factor of $p$ is irreducible
-- statement:
--   Let $p$ and $h$ be bivariate real polynomials and let $h_h$ witness that $h$ belongs to the multiset $\mathrm{normalizedFactors}\,p$ of normalized prime factors of $p$. Then $h$ is irreducible:
--
--   $${\mathrm{Irreducible}\,h.}$$
--
--   This packages the unique-factorization-domain fact that normalized factors are (prime, hence) irreducible elements, licensing the application of all irreducible-case lemmas --- fiber bounds, pair-intersection bounds, nonzero-partial results --- to each factor when decomposing a reducible curve for the factorized Bezout bound.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1413-L1418

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.normalized_factor_irreducible {p h : MvPolynomial (Fin 2) ℝ}
    (hh : h ∈ UniqueFactorizationMonoid.normalizedFactors p) :
    Irreducible h := by sorry
