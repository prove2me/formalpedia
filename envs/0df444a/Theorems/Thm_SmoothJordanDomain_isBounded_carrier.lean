-- Prove2me | Theorems.Thm_SmoothJordanDomain_isBounded_carrier
-- name    : SmoothJordanDomain.isBounded_carrier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:25:02.794812+00:00
-- url     : https://prove2.me/theorems/a6df296c-60a9-51e5-91b4-c0b4c0cb182f
-- title:
--   Smooth Jordan Domain: is Bounded carrier
-- statement:
--   Every represented smooth convex Jordan carrier is bounded.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCompact.lean#L16-L31
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCompact.lean#L16-L31

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_SmoothJordanCompact
set_option autoImplicit false
open Complex Metric Set

theorem SmoothJordanDomain.isBounded_carrier
    (Omega : SmoothJordanDomain) :
    Bornology.IsBounded Omega.carrier := by sorry
