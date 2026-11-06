-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
-- name    : QEC.Coding.PauliSymplectic.exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:19:28.866196+00:00
-- url     : https://prove2.me/theorems/50dacb7c-4d27-4fbe-9e65-4ef04f8d3bed
-- title:
--   Pauli Symplectic: exists z check not commutes css XCheck of hamming Weight lt dual Minimum Distance
-- statement:
--   A low-weight nonzero pure `X` word fails to commute with some `Z` check when
--   the dual minimum distance of the `Z` code is larger than the word weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1319-L1332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1319-L1332

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

theorem QEC.Coding.PauliSymplectic.exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
    (zCode : LinearCode (ZMod 2) ι) {dX : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    {x : Word (ZMod 2) ι} (hx0 : x ≠ 0) (hxlt : HammingWeight x < dX) :
    ∃ z, z ∈ zCode.carrier ∧ ¬ Commutes (cssXCheck x) (cssZCheck z) := by sorry
