-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSQuantumCodeOfDualLe_finrank_carrier
-- name    : QEC.Coding.PauliSymplectic.binaryCSSQuantumCodeOfDualLe_finrank_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:23:42.017031+00:00
-- url     : https://prove2.me/theorems/13ebcfdd-f89b-45ae-ac95-fed80a749331
-- title:
--   Pauli Symplectic: binary CSSQuantum Code Of Dual Le finrank carrier
-- statement:
--   Dimension formula for the actual semantic binary CSS common-fixed carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2861-L2873
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2861-L2873

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

theorem QEC.Coding.PauliSymplectic.binaryCSSQuantumCodeOfDualLe_finrank_carrier
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    Module.finrank Complex
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier =
    2 ^ (Length (ZMod 2) ι - Dimension xCode - Dimension zCode) := by sorry
