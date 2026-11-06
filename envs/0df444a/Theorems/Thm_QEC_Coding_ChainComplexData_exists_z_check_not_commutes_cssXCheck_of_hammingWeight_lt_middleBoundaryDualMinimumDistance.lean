-- Prove2me | Theorems.Thm_QEC_Coding_ChainComplexData_exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_middleBoundaryDualMinimumDistance
-- name    : QEC.Coding.ChainComplexData.exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_middleBoundaryDualMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:29:08.319853+00:00
-- url     : https://prove2.me/theorems/c7b82704-daca-481d-8eb1-4f247b2f45aa
-- title:
--   Chain Complex Data: exists z check not commutes css XCheck of hamming Weight lt middle Boundary Dual Minimum Distance
-- statement:
--   A low-weight nonzero pure `X` word fails to commute with some middle-boundary
--   `Z` check when the middle-boundary code's dual minimum distance is larger than
--   the word weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2917-L2930
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2917-L2930

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

theorem QEC.Coding.ChainComplexData.exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_middleBoundaryDualMinimumDistance
    {ι κ C2 : Type u} [Fintype ι] [Fintype κ]
    [AddCommGroup C2] [Module (ZMod 2) C2]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι) C2)
    {dX : Nat}
    (hminX : MinimumDistance K.middleBoundaryCode.dual dX)
    {x : Word (ZMod 2) ι} (hx0 : x ≠ 0) (hxlt : HammingWeight x < dX) :
    ∃ z, z ∈ K.middleBoundaryCode.carrier ∧
      ¬ PauliSymplectic.Commutes
        (PauliSymplectic.cssXCheck x) (PauliSymplectic.cssZCheck z) := by sorry
