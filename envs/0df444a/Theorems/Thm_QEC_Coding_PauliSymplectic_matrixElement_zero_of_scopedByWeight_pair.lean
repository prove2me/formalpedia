-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_matrixElement_zero_of_scopedByWeight_pair
-- name    : QEC.Coding.PauliSymplectic.matrixElement_zero_of_scopedByWeight_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:23:24.785621+00:00
-- url     : https://prove2.me/theorems/d962c5a9-c963-4361-ba99-ba4a38997030
-- title:
--   Pauli Symplectic: matrix Element zero of scoped By Weight pair
-- statement:
--   Scoped low-weight pair version obtained by combining #177's check separation
--   theorem with the matrix-element bridge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2256-L2276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2256-L2276

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

theorem QEC.Coding.PauliSymplectic.matrixElement_zero_of_scopedByWeight_pair
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {dX dZ t : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    (hbound : 2 * t < min dX dZ)
    {E F : Binary ι}
    (hE : E ∈ scopedByWeight (ι := ι) t)
    (hF : F ∈ scopedByWeight (ι := ι) t)
    (hnontrivial :
      (binaryMul (binaryDagger E) F).vector.xPart ≠ 0 ∨
      (binaryMul (binaryDagger E) F).vector.zPart ≠ 0)
    {ψ φ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    (hφ : φ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier) :
    inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) = 0 := by sorry
