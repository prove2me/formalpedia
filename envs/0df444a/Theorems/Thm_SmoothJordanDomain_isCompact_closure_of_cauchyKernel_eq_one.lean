-- Prove2me | Theorems.Thm_SmoothJordanDomain_isCompact_closure_of_cauchyKernel_eq_one
-- name    : SmoothJordanDomain.isCompact_closure_of_cauchyKernel_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:37.502655+00:00
-- url     : https://prove2.me/theorems/42185826-4a4a-4791-8465-984a1f3ad92b
-- title:
--   Smooth Jordan Domain: is Compact closure of cauchy Kernel eq one
-- statement:
--   The closure of a winding-normalized smooth Jordan carrier is compact.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L102-L107
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L102-L107

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem SmoothJordanDomain.isCompact_closure_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    IsCompact (closure Omega.carrier) := by sorry
