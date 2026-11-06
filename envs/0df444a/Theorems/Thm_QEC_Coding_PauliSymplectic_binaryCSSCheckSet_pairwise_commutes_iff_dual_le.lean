-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSCheckSet_pairwise_commutes_iff_dual_le
-- name    : QEC.Coding.PauliSymplectic.binaryCSSCheckSet_pairwise_commutes_iff_dual_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:27:54.73824+00:00
-- url     : https://prove2.me/theorems/6956190e-74d7-4a35-ad24-a067ce2c8f10
-- title:
--   Pauli Symplectic: binary CSSCheck Set pairwise commutes iff dual le
-- statement:
--   The combined binary CSS check set is pairwise commuting exactly when the `Z`
--   row code lies in the dual of the `X` row code. The reverse containment is
--   equivalent by `LinearCode.le_dual_iff_le_dual`, so no second containment
--   hypothesis is needed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1943-L1960
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1943-L1960

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

theorem QEC.Coding.PauliSymplectic.binaryCSSCheckSet_pairwise_commutes_iff_dual_le
    (xCode zCode : LinearCode (ZMod 2) ι) :
    (∀ P ∈ binaryCSSCheckSet xCode zCode,
      ∀ Q ∈ binaryCSSCheckSet xCode zCode, Commutes P Q) ↔
      zCode.carrier ≤ xCode.dual.carrier := by sorry
