-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_card_lowWord
-- name    : QEC.Coding.BalancedProduct.GVPlus.card_lowWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:44:19.366299+00:00
-- url     : https://prove2.me/theorems/24155610-b290-4c2c-973f-3e9a4d518631
-- title:
--   GVPlus: card low Word
-- statement:
--   Exact Hamming-ball cardinality for binary words on `Fin n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L259-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L259-L261

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

theorem QEC.Coding.BalancedProduct.GVPlus.card_lowWord (n d : Nat) :
    Fintype.card (LowWord n d) = ∑ i ∈ Finset.range d, Nat.choose n i := by sorry
