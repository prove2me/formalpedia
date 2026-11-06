-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_splitComplementABCLabel_splitLabel
-- name    : QEC.Bounds.BPTEntropy.QuditSubsystem.splitComplementABCLabel_splitLabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:47:57.358667+00:00
-- url     : https://prove2.me/theorems/c5bef6f8-77fa-4fb3-82e9-99e43db217a8
-- title:
--   Qudit Subsystem: split Complement ABCLabel split Label
-- statement:
--   The Qudit Subsystem construction uses the split Complement ABCLabel split Label property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1096-L1100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1096-L1100

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

theorem QEC.Bounds.BPTEntropy.QuditSubsystem.splitComplementABCLabel_splitLabel (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label q) :
    splitComplementABCLabel S T hST (S.splitLabel labels).2 =
      (splitABCLabel S T labels).2 := by sorry
