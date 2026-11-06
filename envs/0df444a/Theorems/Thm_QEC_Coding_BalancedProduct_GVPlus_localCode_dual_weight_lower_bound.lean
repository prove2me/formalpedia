-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_localCode_dual_weight_lower_bound
-- name    : QEC.Coding.BalancedProduct.GVPlus.localCode_dual_weight_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:44:52.656802+00:00
-- url     : https://prove2.me/theorems/eaaee005-97ba-4eb2-9bb2-e2b8b1610ad0
-- title:
--   GVPlus: local Code dual weight lower bound
-- statement:
--   Intrinsic carrier form of the dual distance lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L801-L812
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L801-L812

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.PowersetCard
import Mathlib.FieldTheory.Finiteness
import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.BalancedProduct
open QEC.Coding.BalancedProduct.GVPlus
open Classical
attribute [local instance] QEC.Coding.BalancedProduct.GVPlus.localMatrixFintype

theorem QEC.Coding.BalancedProduct.GVPlus.localCode_dual_weight_lower_bound
    (x : Word (ZMod 2) LocalCoordinate)
    (hx : x ∈ localCode.dual.carrier) (hx0 : x ≠ 0) :
    41 ≤ HammingWeight x := by sorry
