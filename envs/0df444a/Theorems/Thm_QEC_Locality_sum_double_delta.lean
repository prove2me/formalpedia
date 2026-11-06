-- Prove2me | Theorems.Thm_QEC_Locality_sum_double_delta
-- name    : QEC.Locality.sum_double_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:40:46.462063+00:00
-- url     : https://prove2.me/theorems/07226dcb-fe14-4b7f-af9e-d344a549e12c
-- title:
--   Locality: sum double delta
-- statement:
--   The Locality construction uses the sum double delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L756-L761
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L756-L761

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.sum_double_delta {α : Type u} [Fintype α] [DecidableEq α]
    (a : α) (c v : Complex) :
    (∑ x : α, c * (if a = x then 1 else 0) * (if x = a then 1 else 0) * v) =
      c * v := by sorry
