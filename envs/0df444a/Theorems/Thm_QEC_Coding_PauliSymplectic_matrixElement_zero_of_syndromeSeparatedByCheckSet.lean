-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_matrixElement_zero_of_syndromeSeparatedByCheckSet
-- name    : QEC.Coding.PauliSymplectic.matrixElement_zero_of_syndromeSeparatedByCheckSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:23:45.8708+00:00
-- url     : https://prove2.me/theorems/0bf49738-1d77-4779-b74d-f02ff9150b76
-- title:
--   Pauli Symplectic: matrix Element zero of syndrome Separated By Check Set
-- statement:
--   Pair version of the matrix-element-zero bridge, phrased through the existing
--   binary product/dagger representative of `E† * F`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2219-L2250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2219-L2250

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

theorem QEC.Coding.PauliSymplectic.matrixElement_zero_of_syndromeSeparatedByCheckSet
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {E F : Binary ι}
    (hsep : syndromeSeparatedByCheckSet (binaryCSSCheckSet xCode zCode) E F)
    {ψ φ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    (hφ : φ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier) :
    inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) = 0 := by sorry
