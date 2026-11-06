-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_mem_binarySupport_add
-- name    : QEC.Coding.PauliSymplectic.mem_binarySupport_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:21:47.52436+00:00
-- url     : https://prove2.me/theorems/70c60c58-4709-4521-8f69-14bc95c82be1
-- title:
--   Pauli Symplectic: mem binary Support add
-- statement:
--   Binary support addition is symmetric difference, stated coordinatewise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L154-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L154-L158

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

theorem QEC.Coding.PauliSymplectic.mem_binarySupport_add (x y : Word (ZMod 2) ι) (i : ι) :
    i ∈ binarySupport (x + y) ↔
      (i ∈ binarySupport x ∧ i ∉ binarySupport y) ∨
        (i ∉ binarySupport x ∧ i ∈ binarySupport y) := by sorry
