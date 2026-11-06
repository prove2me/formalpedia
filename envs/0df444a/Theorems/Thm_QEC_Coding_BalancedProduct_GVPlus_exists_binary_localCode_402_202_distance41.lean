-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_exists_binary_localCode_402_202_distance41
-- name    : QEC.Coding.BalancedProduct.GVPlus.exists_binary_localCode_402_202_distance41
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:48:17.762914+00:00
-- url     : https://prove2.me/theorems/0bf895c2-4325-4fe9-8fcd-1e7b9678c97a
-- title:
--   GVPlus: exists binary local Code 402 202 distance41
-- statement:
--   Fixed-length Gilbert--Varshamov+: an actual binary local code with
--   dimension above half and both primal and dual nonzero weights at least 41.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L816-L827
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean#L816-L827

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

theorem QEC.Coding.BalancedProduct.GVPlus.exists_binary_localCode_402_202_distance41 :
    ∃ C : LinearCode (ZMod 2) LocalCoordinate,
      Length (ZMod 2) LocalCoordinate = 402 ∧
      Dimension C = 202 ∧
      402 / 2 < Dimension C ∧
      (∀ x : Word (ZMod 2) LocalCoordinate,
        x ∈ C.carrier → x ≠ 0 → 41 ≤ HammingWeight x) ∧
      (∀ x : Word (ZMod 2) LocalCoordinate,
        x ∈ C.dual.carrier → x ≠ 0 → 41 ≤ HammingWeight x) := by sorry
