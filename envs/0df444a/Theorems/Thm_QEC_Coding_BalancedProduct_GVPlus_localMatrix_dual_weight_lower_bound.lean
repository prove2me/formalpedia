-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_localMatrix_dual_weight_lower_bound
-- name    : QEC.Coding.BalancedProduct.GVPlus.localMatrix_dual_weight_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:44:39.744194+00:00
-- url     : https://prove2.me/theorems/8cb649c3-a41c-4eca-b828-dd95e42fbd87
-- title:
--   GVPlus: local Matrix dual weight lower bound
-- statement:
--   Every nonzero complementary dual word has weight at least `41`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L763-L768
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L763-L768

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

theorem QEC.Coding.BalancedProduct.GVPlus.localMatrix_dual_weight_lower_bound
    (y : Fin 200 → ZMod 2) (hy : y ≠ 0) :
    41 ≤ HammingWeight (systematicDualEncode localMatrix y) := by sorry
