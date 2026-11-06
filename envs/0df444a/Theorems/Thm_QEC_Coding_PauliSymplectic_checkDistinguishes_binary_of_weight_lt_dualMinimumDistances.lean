-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_checkDistinguishes_binary_of_weight_lt_dualMinimumDistances
-- name    : QEC.Coding.PauliSymplectic.checkDistinguishes_binary_of_weight_lt_dualMinimumDistances
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:23:03.792936+00:00
-- url     : https://prove2.me/theorems/2b68c407-a64e-4eb2-b155-3270d7a53586
-- title:
--   Pauli Symplectic: check Distinguishes binary of weight lt dual Minimum Distances
-- statement:
--   A nontrivial low-weight binary Pauli representative is distinguished by a CSS
--   check under the dual minimum-distance hypotheses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1818-L1850
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1818-L1850

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

theorem QEC.Coding.PauliSymplectic.checkDistinguishes_binary_of_weight_lt_dualMinimumDistances
    (xCode zCode : LinearCode (ZMod 2) ι) {dX dZ : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    {P : Binary ι}
    (hP : P.vector.xPart ≠ 0 ∨ P.vector.zPart ≠ 0)
    (hwt : weight P < min dX dZ) :
    checkDistinguishes (binaryCSSCheckSet xCode zCode) P := by sorry
