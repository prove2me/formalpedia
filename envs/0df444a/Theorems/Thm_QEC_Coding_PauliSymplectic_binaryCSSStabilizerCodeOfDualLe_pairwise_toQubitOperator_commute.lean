-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSStabilizerCodeOfDualLe_pairwise_toQubitOperator_commute
-- name    : QEC.Coding.PauliSymplectic.binaryCSSStabilizerCodeOfDualLe_pairwise_toQubitOperator_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:28:28.941376+00:00
-- url     : https://prove2.me/theorems/9576067d-d17b-4feb-a188-288e0a7f0af2
-- title:
--   Pauli Symplectic: binary CSSStabilizer Code Of Dual Le pairwise to Qubit Operator commute
-- statement:
--   The stabilizer code constructed from binary CSS data has pairwise commuting
--   concrete qubit-register operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2124-L2133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2124-L2133

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

theorem QEC.Coding.PauliSymplectic.binaryCSSStabilizerCodeOfDualLe_pairwise_toQubitOperator_commute
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    ∀ P : Binary ι,
      P ∈ (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).stabilizers →
      ∀ Q : Binary ι,
        Q ∈ (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).stabilizers →
        toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P := by sorry
