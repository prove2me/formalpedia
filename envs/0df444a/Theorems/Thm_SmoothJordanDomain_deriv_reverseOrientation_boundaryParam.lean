-- Prove2me | Theorems.Thm_SmoothJordanDomain_deriv_reverseOrientation_boundaryParam
-- name    : SmoothJordanDomain.deriv_reverseOrientation_boundaryParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:34:06.459751+00:00
-- url     : https://prove2.me/theorems/c4a0c6a2-25cf-515c-b0b5-dae3ae589cc5
-- title:
--   Smooth Jordan Domain: deriv reverse Orientation boundary Param
-- statement:
--   The Smooth Jordan Domain construction uses the deriv reverse Orientation boundary Param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L342-L346
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L342-L346

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
set_option autoImplicit false
open Complex Set
open scoped Real

theorem SmoothJordanDomain.deriv_reverseOrientation_boundaryParam
    (Omega : SmoothJordanDomain) (t : ℝ) :
    deriv Omega.reverseOrientation.boundaryParam t =
      -deriv Omega.boundaryParam (2 * Real.pi - t) := by sorry
