-- Prove2me | Theorems.Thm_SmoothJordanDomain_ellipse_carrier
-- name    : SmoothJordanDomain.ellipse_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:18.553942+00:00
-- url     : https://prove2.me/theorems/78164c5d-07ac-4d87-bda0-3ab004fc3c79
-- title:
--   Smooth Jordan Domain: ellipse carrier
-- statement:
--   The Smooth Jordan Domain construction uses the ellipse carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean#L124-L127
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean#L124-L127

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Convex.ContinuousLinearEquiv
import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
open SmoothJordanDomain

theorem SmoothJordanDomain.ellipse_carrier (c : ℂ) (e : ℂ ≃L[ℝ] ℂ)
    (R : ℝ) (hR : 0 < R) :
    (ellipse c e R hR).carrier =
      (fun z => c + z) '' (e '' Metric.ball 0 R) := by sorry

attribute [defeq] SmoothJordanDomain.ellipse_carrier
