-- Prove2me | Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
-- name    : SmoothJordanDomain.reverseOrientation_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:30:58.811255+00:00
-- url     : https://prove2.me/theorems/b6a95b00-8e2d-5c96-83dc-0fd32c9bc5d3
-- title:
--   Smooth Jordan Domain: reverse Orientation carrier
-- statement:
--   The Smooth Jordan Domain construction uses the reverse Orientation carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L333-L335
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L333-L335

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
set_option autoImplicit false
open Complex Set
open scoped Real

theorem SmoothJordanDomain.reverseOrientation_carrier
    (Omega : SmoothJordanDomain) :
    Omega.reverseOrientation.carrier = Omega.carrier := by sorry

attribute [defeq] SmoothJordanDomain.reverseOrientation_carrier
