-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_binaryMul_right
-- name    : QEC.Coding.PauliSymplectic.commutes_binaryMul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:19:34.611076+00:00
-- url     : https://prove2.me/theorems/5e618354-de43-4936-ab35-a54bf3a218ca
-- title:
--   Pauli Symplectic: commutes binary Mul right
-- statement:
--   Commutation with two binary Paulis is preserved by their product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1405-L1418
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1405-L1418

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

theorem QEC.Coding.PauliSymplectic.commutes_binaryMul_right {E P Q : Binary ι}
    (hP : Commutes E P) (hQ : Commutes E Q) :
    Commutes E (binaryMul P Q) := by sorry
