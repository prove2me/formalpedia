-- Prove2me | Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
-- name    : SmoothJordanDomain.reverseOrientation_boundaryParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:31:15.211343+00:00
-- url     : https://prove2.me/theorems/6afe7589-c1c4-4894-85e6-9e0dc1655978
-- title:
--   Smooth Jordan Domain: reverse Orientation boundary Param
-- statement:
--   The Smooth Jordan Domain construction uses the reverse Orientation boundary Param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L337-L340
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L337-L340

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
set_option autoImplicit false
open Complex Set
open scoped Real

theorem SmoothJordanDomain.reverseOrientation_boundaryParam
    (Omega : SmoothJordanDomain) (t : ℝ) :
    Omega.reverseOrientation.boundaryParam t =
      Omega.boundaryParam (2 * Real.pi - t) := by sorry

attribute [defeq] SmoothJordanDomain.reverseOrientation_boundaryParam
