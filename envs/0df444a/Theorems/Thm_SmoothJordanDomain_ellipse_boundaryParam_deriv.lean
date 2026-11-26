-- Prove2me | Theorems.Thm_SmoothJordanDomain_ellipse_boundaryParam_deriv
-- name    : SmoothJordanDomain.ellipse_boundaryParam_deriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:37.128886+00:00
-- url     : https://prove2.me/theorems/4f972276-747a-45ec-ab4b-4a128c1b0a87
-- title:
--   Smooth Jordan Domain: ellipse boundary Param deriv
-- statement:
--   The Smooth Jordan Domain construction uses the ellipse boundary Param deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean#L134-L141
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean#L134-L141

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Convex.ContinuousLinearEquiv
import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
open SmoothJordanDomain

theorem SmoothJordanDomain.ellipse_boundaryParam_deriv (c : ℂ)
    (e : ℂ ≃L[ℝ] ℂ) (R : ℝ) (hR : 0 < R) (t : ℝ) :
    deriv (ellipse c e R hR).boundaryParam t =
      e (circleMap 0 R t * I) := by sorry
