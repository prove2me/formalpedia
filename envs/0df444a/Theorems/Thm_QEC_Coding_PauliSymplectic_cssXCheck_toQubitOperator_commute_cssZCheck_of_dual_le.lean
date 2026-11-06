-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_cssXCheck_toQubitOperator_commute_cssZCheck_of_dual_le
-- name    : QEC.Coding.PauliSymplectic.cssXCheck_toQubitOperator_commute_cssZCheck_of_dual_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:26:23.223667+00:00
-- url     : https://prove2.me/theorems/be3037aa-2821-4a7b-a673-8b1307be3fb4
-- title:
--   Pauli Symplectic: css XCheck to Qubit Operator commute css ZCheck of dual le
-- statement:
--   Binary CSS X/Z checks commute as concrete qubit-register operators under the
--   dual-containment convention `zCode ≤ xCode.dual`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1217-L1224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1217-L1224

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

theorem QEC.Coding.PauliSymplectic.cssXCheck_toQubitOperator_commute_cssZCheck_of_dual_le
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {x z : Word (ZMod 2) ι}
    (hx : x ∈ xCode.carrier) (hz : z ∈ zCode.carrier) :
    toQubitOperator (cssXCheck x) * toQubitOperator (cssZCheck z) =
      toQubitOperator (cssZCheck z) * toQubitOperator (cssXCheck x) := by sorry
