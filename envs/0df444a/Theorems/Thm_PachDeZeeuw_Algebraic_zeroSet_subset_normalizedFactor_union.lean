-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_zeroSet_subset_normalizedFactor_union
-- name    : PachDeZeeuw.Algebraic.zeroSet_subset_normalizedFactor_union
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:31.500818+00:00
-- url     : https://prove2.me/theorems/31a75df2-73f0-4752-a6ec-cb9f74b9c8fd
-- title:
--   Zero set of $p$ covered by zero sets of its normalized factors
-- statement:
--   Let $p$ be a nonzero bivariate real polynomial ($h_{p0} : p \neq 0$). Then its plane zero set is covered by the zero sets of its normalized factors:
--
--   $${\mathrm{PlaneCurveZeroSet}\,p \subseteq \bigcup_{h \in (\mathrm{normalizedFactors}\,p).\mathrm{toFinset}} \mathrm{PlaneCurveZeroSet}\,h.}$$
--
--   This is the geometric counterpart of unique factorization: since $p$ equals (up to a unit) the product of its normalized factors, every zero of $p$ is a zero of some factor. It is the reduction step that lifts per-irreducible-component intersection bounds to reducible curves in the factorized Bezout bound.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1506-L1532

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.zeroSet_subset_normalizedFactor_union {p : MvPolynomial (Fin 2) ℝ} (hp0 : p ≠ 0) :
    PlaneCurveZeroSet p ⊆
      ⋃ h ∈ (UniqueFactorizationMonoid.normalizedFactors p).toFinset,
        PlaneCurveZeroSet h := by sorry
