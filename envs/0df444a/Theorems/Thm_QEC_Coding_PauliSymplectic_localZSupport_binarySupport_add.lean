-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_localZSupport_binarySupport_add
-- name    : QEC.Coding.PauliSymplectic.localZSupport_binarySupport_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:22:05.92472+00:00
-- url     : https://prove2.me/theorems/a5d94dde-8abd-43a6-99b9-1863e4f9c159
-- title:
--   Pauli Symplectic: local ZSupport binary Support add
-- statement:
--   The Pauli Symplectic construction uses the local ZSupport binary Support add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L640-L645
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L640-L645

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.localZSupport_binarySupport_add (x y : Word (ZMod 2) ι) :
    Semantics.Qubit.localZSupport (binarySupport (x + y)) =
      Semantics.Qubit.localZSupport (binarySupport x) *
        Semantics.Qubit.localZSupport (binarySupport y) := by sorry
