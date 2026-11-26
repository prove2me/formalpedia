-- Prove2me | Theorems.Thm_SmoothJordanDomain_translate_carrier
-- name    : SmoothJordanDomain.translate_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:04.477421+00:00
-- url     : https://prove2.me/theorems/cc90483c-46b0-481c-aa7a-ab83b8e0753f
-- title:
--   Smooth Jordan Domain: translate carrier
-- statement:
--   The Smooth Jordan Domain construction uses the translate carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean#L102-L103
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean#L102-L103

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Convex.ContinuousLinearEquiv
import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
open SmoothJordanDomain

theorem SmoothJordanDomain.translate_carrier (Omega : SmoothJordanDomain) (c : ℂ) :
    (Omega.translate c).carrier = (fun z => c + z) '' Omega.carrier := by sorry

attribute [defeq] SmoothJordanDomain.translate_carrier
