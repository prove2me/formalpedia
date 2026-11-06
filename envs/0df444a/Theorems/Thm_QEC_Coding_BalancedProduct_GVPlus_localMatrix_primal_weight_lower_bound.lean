-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_localMatrix_primal_weight_lower_bound
-- name    : QEC.Coding.BalancedProduct.GVPlus.localMatrix_primal_weight_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:44:27.031081+00:00
-- url     : https://prove2.me/theorems/df8c5df5-43fd-46e4-9e79-fc2ab87b2fde
-- title:
--   GVPlus: local Matrix primal weight lower bound
-- statement:
--   Every nonzero generated local word has weight at least `41`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L755-L760
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L755-L760

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

theorem QEC.Coding.BalancedProduct.GVPlus.localMatrix_primal_weight_lower_bound
    (m : Fin 202 → ZMod 2) (hm : m ≠ 0) :
    41 ≤ HammingWeight (systematicEncode localMatrix m) := by sorry
