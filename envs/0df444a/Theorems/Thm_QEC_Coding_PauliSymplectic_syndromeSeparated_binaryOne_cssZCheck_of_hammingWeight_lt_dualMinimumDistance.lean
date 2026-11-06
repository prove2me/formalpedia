-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_syndromeSeparated_binaryOne_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
-- name    : QEC.Coding.PauliSymplectic.syndromeSeparated_binaryOne_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:27:49.613694+00:00
-- url     : https://prove2.me/theorems/291c800f-f36f-44a3-8616-d84cc35a8cb1
-- title:
--   Pauli Symplectic: syndrome Separated binary One css ZCheck of hamming Weight lt dual Minimum Distance
-- statement:
--   Identity versus a low-weight nonzero pure `Z` error is separated by a CSS
--   check under the dual-distance hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1872-L1880
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1872-L1880

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

theorem QEC.Coding.PauliSymplectic.syndromeSeparated_binaryOne_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
    (xCode zCode : LinearCode (ZMod 2) ι) {dZ : Nat}
    (hminZ : MinimumDistance xCode.dual dZ)
    {z : Word (ZMod 2) ι} (hz0 : z ≠ 0) (hzlt : HammingWeight z < dZ) :
    syndromeSeparatedByCheckSet (binaryCSSCheckSet xCode zCode)
      (binaryOne (ι := ι)) (cssZCheck z) := by sorry
