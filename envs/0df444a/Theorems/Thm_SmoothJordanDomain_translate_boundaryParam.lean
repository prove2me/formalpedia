-- Prove2me | Theorems.Thm_SmoothJordanDomain_translate_boundaryParam
-- name    : SmoothJordanDomain.translate_boundaryParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:12.707946+00:00
-- url     : https://prove2.me/theorems/b516132e-02f7-55bc-a1d5-3f0ea72cd364
-- title:
--   Smooth Jordan Domain: translate boundary Param
-- statement:
--   The Smooth Jordan Domain construction uses the translate boundary Param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean#L105-L106
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean#L105-L106

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Convex.ContinuousLinearEquiv
import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
open SmoothJordanDomain

theorem SmoothJordanDomain.translate_boundaryParam (Omega : SmoothJordanDomain) (c : ℂ) :
    (Omega.translate c).boundaryParam = fun t => c + Omega.boundaryParam t := by sorry

attribute [defeq] SmoothJordanDomain.translate_boundaryParam
