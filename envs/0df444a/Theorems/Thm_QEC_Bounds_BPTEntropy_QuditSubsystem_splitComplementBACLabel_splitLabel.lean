-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_splitComplementBACLabel_splitLabel
-- name    : QEC.Bounds.BPTEntropy.QuditSubsystem.splitComplementBACLabel_splitLabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:48:46.194143+00:00
-- url     : https://prove2.me/theorems/970b3c6b-863e-41a8-873f-3654657a69c4
-- title:
--   Qudit Subsystem: split Complement BACLabel split Label
-- statement:
--   The Qudit Subsystem construction uses the split Complement BACLabel split Label property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1304-L1308
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1304-L1308

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u
open QEC.Bounds.BPTEntropy.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι -> Nat}

theorem QEC.Bounds.BPTEntropy.QuditSubsystem.splitComplementBACLabel_splitLabel (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label q) :
    splitComplementBACLabel S T hST (T.splitLabel labels).2 =
      ((splitABCLabel S T labels).1, (splitABCLabel S T labels).2.2) := by sorry
