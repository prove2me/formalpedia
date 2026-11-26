-- Prove2me | Theorems.Thm_SmoothJordanDomain_ellipse_boundaryParam
-- name    : SmoothJordanDomain.ellipse_boundaryParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:30.376896+00:00
-- url     : https://prove2.me/theorems/7b507c0f-9cec-5c40-be99-2140d932fada
-- title:
--   Smooth Jordan Domain: ellipse boundary Param
-- statement:
--   The Smooth Jordan Domain construction uses the ellipse boundary Param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean#L129-L132
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean#L129-L132

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Convex.ContinuousLinearEquiv
import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
open SmoothJordanDomain

theorem SmoothJordanDomain.ellipse_boundaryParam (c : ℂ) (e : ℂ ≃L[ℝ] ℂ)
    (R : ℝ) (hR : 0 < R) :
    (ellipse c e R hR).boundaryParam =
      fun t => c + e (circleMap 0 R t) := by sorry

attribute [defeq] SmoothJordanDomain.ellipse_boundaryParam
