-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
-- name    : QEC.Coding.PauliSymplectic.exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:19:32.717798+00:00
-- url     : https://prove2.me/theorems/9a6cc31f-8742-4087-ad8a-5068ea512e2d
-- title:
--   Pauli Symplectic: exists x check not commutes css ZCheck of hamming Weight lt dual Minimum Distance
-- statement:
--   A low-weight nonzero pure `Z` word fails to commute with some `X` check when
--   the dual minimum distance of the `X` code is larger than the word weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1339-L1376
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1339-L1376

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

theorem QEC.Coding.PauliSymplectic.exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
    (xCode : LinearCode (ZMod 2) ι) {dZ : Nat}
    (hminZ : MinimumDistance xCode.dual dZ)
    {z : Word (ZMod 2) ι} (hz0 : z ≠ 0) (hzlt : HammingWeight z < dZ) :
    ∃ x, x ∈ xCode.carrier ∧ ¬ Commutes (cssZCheck z) (cssXCheck x) := by sorry
