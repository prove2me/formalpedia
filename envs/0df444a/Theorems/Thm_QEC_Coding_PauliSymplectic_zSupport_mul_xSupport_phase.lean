-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_zSupport_mul_xSupport_phase
-- name    : QEC.Coding.PauliSymplectic.zSupport_mul_xSupport_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:25:39.485819+00:00
-- url     : https://prove2.me/theorems/7670fa96-475d-42c8-b3aa-b647ae7d8e4c
-- title:
--   Pauli Symplectic: z Support mul x Support phase
-- statement:
--   The binary support phase for moving a concrete `Z` support past a concrete `X` support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L786-L794
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L786-L794

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

theorem QEC.Coding.PauliSymplectic.zSupport_mul_xSupport_phase (z x : Word (ZMod 2) ι) :
    Semantics.Qubit.localZSupport (binarySupport z) *
        Semantics.Qubit.localXSupport (binarySupport x) =
      binarySwapPhase x z •
        (Semantics.Qubit.localXSupport (binarySupport x) *
          Semantics.Qubit.localZSupport (binarySupport z)) := by sorry
