-- Prove2me | Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
-- name    : SmoothJordanDomain.isBounded_carrier_of_cauchyKernel_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:06:24.359301+00:00
-- url     : https://prove2.me/theorems/a08005f8-ec2f-5b81-aaad-185a02dceaf8
-- title:
--   Smooth Jordan Domain: is Bounded carrier of cauchy Kernel eq one
-- statement:
--   If the scalar winding kernel is normalized to one throughout the carrier,
--   then exterior Cauchy-transform decay forces that carrier to be bounded.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L73-L99
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L73-L99

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem SmoothJordanDomain.isBounded_carrier_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    Bornology.IsBounded Omega.carrier := by sorry
