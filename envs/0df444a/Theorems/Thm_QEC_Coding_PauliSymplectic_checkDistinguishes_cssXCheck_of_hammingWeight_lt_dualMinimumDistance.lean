-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_checkDistinguishes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
-- name    : QEC.Coding.PauliSymplectic.checkDistinguishes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:23:05.108032+00:00
-- url     : https://prove2.me/theorems/b2810142-180d-46c0-8a24-61e3c8e62ca0
-- title:
--   Pauli Symplectic: check Distinguishes css XCheck of hamming Weight lt dual Minimum Distance
-- statement:
--   A low-weight nonzero pure `X` word is distinguished from identity by some
--   `Z` check in the binary CSS check set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1787-L1796
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1787-L1796

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

theorem QEC.Coding.PauliSymplectic.checkDistinguishes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
    (xCode zCode : LinearCode (ZMod 2) ι) {dX : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    {x : Word (ZMod 2) ι} (hx0 : x ≠ 0) (hxlt : HammingWeight x < dX) :
    checkDistinguishes (binaryCSSCheckSet xCode zCode) (cssXCheck x) := by sorry
