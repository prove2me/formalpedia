-- Prove2me | Theorems.Thm_QEC_Coding_ChainComplexData_exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_firstCoboundaryDualMinimumDistance
-- name    : QEC.Coding.ChainComplexData.exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_firstCoboundaryDualMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:28:59.35712+00:00
-- url     : https://prove2.me/theorems/27bddc4f-f104-4011-a38b-7bfac6a54faa
-- title:
--   Chain Complex Data: exists x check not commutes css ZCheck of hamming Weight lt first Coboundary Dual Minimum Distance
-- statement:
--   A low-weight nonzero pure `Z` word fails to commute with some first-coboundary
--   `X` check when the first-coboundary code's dual minimum distance is larger than
--   the word weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2937-L2950
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2937-L2950

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
open QEC.Coding.ChainComplexData

theorem QEC.Coding.ChainComplexData.exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_firstCoboundaryDualMinimumDistance
    {ι κ C2 : Type u} [Fintype ι] [Fintype κ]
    [AddCommGroup C2] [Module (ZMod 2) C2]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι) C2)
    {dZ : Nat}
    (hminZ : MinimumDistance K.firstCoboundaryCheckCode.dual dZ)
    {z : Word (ZMod 2) ι} (hz0 : z ≠ 0) (hzlt : HammingWeight z < dZ) :
    ∃ x, x ∈ K.firstCoboundaryCheckCode.carrier ∧
      ¬ PauliSymplectic.Commutes
        (PauliSymplectic.cssZCheck z) (PauliSymplectic.cssXCheck x) := by sorry
