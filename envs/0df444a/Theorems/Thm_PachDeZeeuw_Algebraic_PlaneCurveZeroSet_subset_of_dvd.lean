-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_PlaneCurveZeroSet_subset_of_dvd
-- name    : PachDeZeeuw.Algebraic.PlaneCurveZeroSet_subset_of_dvd
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:36:34.917157+00:00
-- url     : https://prove2.me/theorems/a383df74-622b-4132-bedd-f87ed12b4e7b
-- title:
--   Zero-set inclusion for divisibility of plane polynomials
-- statement:
--   Let $p$ and $q$ be bivariate real polynomials (elements of $\mathrm{MvPolynomial}(\mathrm{Fin}\,2, \mathbb{R})$), and assume $p$ divides $q$ ($p \mid q$). Then the real plane zero set of $p$ is contained in that of $q$:
--
--   $${Z}(p) \subseteq {Z}(q),$$
--
--   where ${Z}(p) = \{x \in \mathbb{R}^2 \mid p(x) = 0\}$ is `PlaneCurveZeroSet`. In words, every common real zero of the divisor polynomial is a zero of the multiple. This monotonicity lemma is used throughout the project whenever a curve is factored: it lets one replace a polynomial by any of its divisors (or pass zero-set inclusions through factorizations) when bounding intersections and singular loci.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L136-L142

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.PlaneCurveZeroSet_subset_of_dvd {p q : MvPolynomial (Fin 2) ℝ}
    (hpq : p ∣ q) : PlaneCurveZeroSet p ⊆ PlaneCurveZeroSet q := by sorry
