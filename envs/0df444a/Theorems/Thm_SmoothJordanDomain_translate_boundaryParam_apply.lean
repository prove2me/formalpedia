-- Prove2me | Theorems.Thm_SmoothJordanDomain_translate_boundaryParam_apply
-- name    : SmoothJordanDomain.translate_boundaryParam_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:27.237476+00:00
-- url     : https://prove2.me/theorems/5d4cd73a-fafc-4b8c-b994-99053640e116
-- title:
--   Smooth Jordan Domain: translate boundary Param apply
-- statement:
--   The Smooth Jordan Domain construction uses the translate boundary Param apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean#L108-L110
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean#L108-L110

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Convex.ContinuousLinearEquiv
import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
open SmoothJordanDomain

theorem SmoothJordanDomain.translate_boundaryParam_apply (Omega : SmoothJordanDomain)
    (c : ℂ) (t : ℝ) :
    (Omega.translate c).boundaryParam t = c + Omega.boundaryParam t := by sorry

attribute [defeq] SmoothJordanDomain.translate_boundaryParam_apply
