-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_inner_toQubitOperator_eq_zero_of_checkDistinguishes
-- name    : QEC.Coding.PauliSymplectic.inner_toQubitOperator_eq_zero_of_checkDistinguishes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:23:26.297193+00:00
-- url     : https://prove2.me/theorems/fc65e713-4d40-4bcb-aa26-4143cf459018
-- title:
--   Pauli Symplectic: inner to Qubit Operator eq zero of check Distinguishes
-- statement:
--   A CSS check that distinguishes `P` from identity forces the corresponding
--   matrix element to vanish on the semantic binary CSS common-fixed carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2167-L2213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2167-L2213

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

theorem QEC.Coding.PauliSymplectic.inner_toQubitOperator_eq_zero_of_checkDistinguishes
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {P : Binary ι}
    (hsep : checkDistinguishes (binaryCSSCheckSet xCode zCode) P)
    {ψ φ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    (hφ : φ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier) :
    inner Complex (toQubitOperator P ψ) φ = 0 := by sorry
