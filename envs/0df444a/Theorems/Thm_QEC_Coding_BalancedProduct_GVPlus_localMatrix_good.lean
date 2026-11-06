-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_localMatrix_good
-- name    : QEC.Coding.BalancedProduct.GVPlus.localMatrix_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:42:42.540702+00:00
-- url     : https://prove2.me/theorems/d4eafaa5-0cf9-46f5-8b65-a969d9327d31
-- title:
--   GVPlus: local Matrix good
-- statement:
--   The GVPlus construction uses the local Matrix good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L751-L752
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L751-L752

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

theorem QEC.Coding.BalancedProduct.GVPlus.localMatrix_good : ¬Bad localMatrix := by sorry
