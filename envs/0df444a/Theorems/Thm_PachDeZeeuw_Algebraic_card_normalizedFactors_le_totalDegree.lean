-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_card_normalizedFactors_le_totalDegree
-- name    : PachDeZeeuw.Algebraic.card_normalizedFactors_le_totalDegree
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:36:56.405981+00:00
-- url     : https://prove2.me/theorems/3ca4dd17-7b06-4dc8-89c3-1c3d5d170cc5
-- title:
--   Number of normalized factors bounded by total degree
-- statement:
--   Let $p$ be a nonzero bivariate real polynomial ($p \ne 0$ in $\mathrm{MvPolynomial}(\mathrm{Fin}\,2, \mathbb{R})$). Then the number of factors in its normalized factorization is bounded by its total degree:
--
--   $$|\mathrm{normalizedFactors}(p)| \le \mathrm{totalDegree}(p).$$
--
--   This factor-counting estimate is the bookkeeping input to the factorized B\u00e9zout bound: it controls how many irreducible-pair intersections must be union-bounded when both curves are split into factors.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1475-L1496

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.card_normalizedFactors_le_totalDegree {p : MvPolynomial (Fin 2) ℝ} (hp0 : p ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors p).card ≤ p.totalDegree := by sorry
