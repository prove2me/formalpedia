-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_systematicDualEncode_injective
-- name    : QEC.Coding.BalancedProduct.GVPlus.systematicDualEncode_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:47:26.176199+00:00
-- url     : https://prove2.me/theorems/6a62218c-90b5-4e63-9c0d-ae5ae53d5708
-- title:
--   GVPlus: systematic Dual Encode injective
-- statement:
--   Complementary systematic dual encoding is injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L178-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L178-L183

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

theorem QEC.Coding.BalancedProduct.GVPlus.systematicDualEncode_injective {k r : Nat}
    (A : Matrix (Fin k) (Fin r) (ZMod 2)) :
    Function.Injective (systematicDualEncode A) := by sorry
