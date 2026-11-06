-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_zSupportPhase_binarySupport_add
-- name    : QEC.Coding.PauliSymplectic.zSupportPhase_binarySupport_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:22:04.916869+00:00
-- url     : https://prove2.me/theorems/48e97eca-5ac0-44e2-9b1f-583c6cb50a7b
-- title:
--   Pauli Symplectic: z Support Phase binary Support add
-- statement:
--   The Pauli Symplectic construction uses the z Support Phase binary Support add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L618-L638
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L618-L638

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
omit [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.zSupportPhase_binarySupport_add (x y : Word (ZMod 2) ι)
    (bits : Semantics.Qubit.Bitstring ι) :
    Semantics.Qubit.zSupportPhase (binarySupport (x + y)) bits =
      Semantics.Qubit.zSupportPhase (binarySupport x) bits *
        Semantics.Qubit.zSupportPhase (binarySupport y) bits := by sorry
