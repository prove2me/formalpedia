-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_localCode_length
-- name    : QEC.Coding.BalancedProduct.GVPlus.localCode_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:44:41.044034+00:00
-- url     : https://prove2.me/theorems/58663cfe-c683-4f1e-8d7e-1bf76c17493f
-- title:
--   GVPlus: local Code length
-- statement:
--   The local code has block length exactly `402`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L775-L776
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L775-L776

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

theorem QEC.Coding.BalancedProduct.GVPlus.localCode_length : Length (ZMod 2) LocalCoordinate = 402 := by sorry
