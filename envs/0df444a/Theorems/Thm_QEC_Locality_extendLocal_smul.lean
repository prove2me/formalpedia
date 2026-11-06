-- Prove2me | Theorems.Thm_QEC_Locality_extendLocal_smul
-- name    : QEC.Locality.extendLocal_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:23.589083+00:00
-- url     : https://prove2.me/theorems/7f160032-dd83-4288-a061-2b2b3747f301
-- title:
--   Locality: extend Local smul
-- statement:
--   The Locality construction uses the extend Local smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L978-L985
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L978-L985

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

theorem QEC.Locality.extendLocal_smul (S : FiniteSubsystem ι) (c : Complex)
    (A : Operator S.selectedSystem) :
    S.extendLocal (c • A) = c • S.extendLocal A := by sorry
