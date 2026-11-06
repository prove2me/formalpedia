-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_wordPairing_systematicDualEncode_systematicEncode
-- name    : QEC.Coding.BalancedProduct.GVPlus.wordPairing_systematicDualEncode_systematicEncode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:43:41.102277+00:00
-- url     : https://prove2.me/theorems/48464705-b659-4963-bb9b-c35a919ee635
-- title:
--   GVPlus: word Pairing systematic Dual Encode systematic Encode
-- statement:
--   A systematic word is orthogonal to its complementary dual word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L101-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L101-L127

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

theorem QEC.Coding.BalancedProduct.GVPlus.wordPairing_systematicDualEncode_systematicEncode {k r : Nat}
    (A : Matrix (Fin k) (Fin r) (ZMod 2))
    (y : Fin r → ZMod 2) (m : Fin k → ZMod 2) :
    wordPairing (systematicDualEncode A y) (systematicEncode A m) = 0 := by sorry
