-- Prove2me | Theorems.Thm_SmoothJordanDomain_translate_boundaryParam_deriv
-- name    : SmoothJordanDomain.translate_boundaryParam_deriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:46.538807+00:00
-- url     : https://prove2.me/theorems/8f87d313-3a64-4d47-aa4d-73a7b251b5bf
-- title:
--   Smooth Jordan Domain: translate boundary Param deriv
-- statement:
--   The Smooth Jordan Domain construction uses the translate boundary Param deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean#L112-L116
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean#L112-L116

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Convex.ContinuousLinearEquiv
import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
open SmoothJordanDomain

theorem SmoothJordanDomain.translate_boundaryParam_deriv (Omega : SmoothJordanDomain)
    (c : ℂ) (t : ℝ) :
    deriv (Omega.translate c).boundaryParam t =
      deriv Omega.boundaryParam t := by sorry
