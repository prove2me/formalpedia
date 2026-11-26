-- Prove2me | Theorems.Thm_SmoothJordanDomain_isCompact_closure
-- name    : SmoothJordanDomain.isCompact_closure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:25:22.251852+00:00
-- url     : https://prove2.me/theorems/14a47b7d-79a2-424e-a003-714feff2f53e
-- title:
--   Smooth Jordan Domain: is Compact closure
-- statement:
--   The closure of every represented smooth convex Jordan carrier is compact.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCompact.lean#L34-L37
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCompact.lean#L34-L37

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_SmoothJordanCompact
set_option autoImplicit false
open Complex Metric Set

theorem SmoothJordanDomain.isCompact_closure
    (Omega : SmoothJordanDomain) :
    IsCompact (closure Omega.carrier) := by sorry
