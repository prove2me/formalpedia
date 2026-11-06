-- Prove2me | Theorems.Thm_QEC_Locality_bitstringWord_add_eq_zero_iff
-- name    : QEC.Locality.bitstringWord_add_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:39:59.019892+00:00
-- url     : https://prove2.me/theorems/3ba80dfe-00b9-4296-8556-2bfc8bb3d40d
-- title:
--   Locality: bitstring Word add eq zero iff
-- statement:
--   The Locality construction uses the bitstring Word add eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L529-L539
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L529-L539

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

theorem QEC.Locality.bitstringWord_add_eq_zero_iff {α : Type u} [Fintype α] [DecidableEq α]
    (a b : Qubit.Bitstring α) :
    PauliSymplectic.bitstringWordEquiv α b +
        PauliSymplectic.bitstringWordEquiv α a = 0 ↔ b = a := by sorry
