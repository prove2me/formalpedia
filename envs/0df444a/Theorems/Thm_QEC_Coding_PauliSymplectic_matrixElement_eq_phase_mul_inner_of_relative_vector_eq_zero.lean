-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_matrixElement_eq_phase_mul_inner_of_relative_vector_eq_zero
-- name    : QEC.Coding.PauliSymplectic.matrixElement_eq_phase_mul_inner_of_relative_vector_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:22:31.116136+00:00
-- url     : https://prove2.me/theorems/fbd64c84-348f-4cbf-b781-5b3f453e4045
-- title:
--   Pauli Symplectic: matrix Element eq phase mul inner of relative vector eq zero
-- statement:
--   Phase-only relative Paulis give the scalar branch of the KL matrix element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L990-L1027
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L990-L1027

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

theorem QEC.Coding.PauliSymplectic.matrixElement_eq_phase_mul_inner_of_relative_vector_eq_zero
    {E F : Binary ι}
    (hx : (binaryMul (binaryDagger E) F).vector.xPart = 0)
    (hz : (binaryMul (binaryDagger E) F).vector.zPart = 0)
    {ψ φ : Semantics.Qubit.QubitRegister ι} :
    inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) =
      binaryPhaseScalar (binaryMul (binaryDagger E) F).phase * inner Complex ψ φ := by sorry
