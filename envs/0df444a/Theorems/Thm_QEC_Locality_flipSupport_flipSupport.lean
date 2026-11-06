-- Prove2me | Theorems.Thm_QEC_Locality_flipSupport_flipSupport
-- name    : QEC.Locality.flipSupport_flipSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:37:54.731711+00:00
-- url     : https://prove2.me/theorems/9dd8b457-0954-4eae-9284-eb821490ec84
-- title:
--   Locality: flip Support flip Support
-- statement:
--   The Locality construction uses the flip Support flip Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L27-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L27-L31

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

theorem QEC.Locality.flipSupport_flipSupport {α : Type u} [DecidableEq α]
    (s : Finset α) (bits : Qubit.Bitstring α) :
    Qubit.flipSupport s (Qubit.flipSupport s bits) = bits := by sorry
