-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_mem_dual_systematicCode_iff
-- name    : QEC.Coding.BalancedProduct.GVPlus.mem_dual_systematicCode_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:43:33.444194+00:00
-- url     : https://prove2.me/theorems/7188170b-9c8d-4e9c-95ad-1bf21d1c5cda
-- title:
--   GVPlus: mem dual systematic Code iff
-- statement:
--   Every word in the dual row space has the complementary systematic form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L130-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L130-L175

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

theorem QEC.Coding.BalancedProduct.GVPlus.mem_dual_systematicCode_iff {k r : Nat}
    (A : Matrix (Fin k) (Fin r) (ZMod 2))
    (x : Sum (Fin k) (Fin r) → ZMod 2) :
    x ∈ (systematicCode A).dual.carrier ↔
      ∃ y : Fin r → ZMod 2, systematicDualEncode A y = x := by sorry
