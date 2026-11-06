-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_cssXCheck_toQubitOperator_commute_cssZCheck_of_mem_dual
-- name    : QEC.Coding.PauliSymplectic.cssXCheck_toQubitOperator_commute_cssZCheck_of_mem_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:22:35.348474+00:00
-- url     : https://prove2.me/theorems/cd2456d0-8aa1-4eec-b220-dc0f4a04b4b8
-- title:
--   Pauli Symplectic: css XCheck to Qubit Operator commute css ZCheck of mem dual
-- statement:
--   Binary CSS X/Z checks commute as concrete qubit-register operators when the
--   `Z` word lies in the dual of the classical code containing the `X` word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1205-L1211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1205-L1211

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

theorem QEC.Coding.PauliSymplectic.cssXCheck_toQubitOperator_commute_cssZCheck_of_mem_dual
    (C : LinearCode (ZMod 2) ι) {x z : Word (ZMod 2) ι}
    (hx : x ∈ C.carrier) (hz : z ∈ C.dual.carrier) :
    toQubitOperator (cssXCheck x) * toQubitOperator (cssZCheck z) =
      toQubitOperator (cssZCheck z) * toQubitOperator (cssXCheck x) := by sorry
