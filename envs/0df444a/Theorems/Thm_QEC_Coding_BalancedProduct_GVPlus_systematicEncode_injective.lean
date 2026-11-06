-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_systematicEncode_injective
-- name    : QEC.Coding.BalancedProduct.GVPlus.systematicEncode_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:43:46.421347+00:00
-- url     : https://prove2.me/theorems/90ed8e8e-9814-49b3-b444-2a5d5a1ee24c
-- title:
--   GVPlus: systematic Encode injective
-- statement:
--   The identity coordinates make every systematic encoding injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L64-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L64-L69

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

theorem QEC.Coding.BalancedProduct.GVPlus.systematicEncode_injective {k r : Nat}
    (A : Matrix (Fin k) (Fin r) (ZMod 2)) :
    Function.Injective (systematicEncode A) := by sorry
