-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_complementBACFactorization_apply_basis
-- name    : QEC.Bounds.BPTEntropy.QuditSubsystem.complementBACFactorization_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:48:01.689795+00:00
-- url     : https://prove2.me/theorems/953baacd-b719-480f-b22b-2807b9120a9f
-- title:
--   Qudit Subsystem: complement BACFactorization apply basis
-- statement:
--   The Qudit Subsystem construction uses the complement BACFactorization apply basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1290-L1302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1290-L1302

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

theorem QEC.Bounds.BPTEntropy.QuditSubsystem.complementBACFactorization_apply_basis (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label T.complementDimensions) :
    complementBACFactorization S T hST
      (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex labels) =
      (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
        (splitComplementBACLabel S T hST labels).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun
        (Qudit.Label (unionSubsystem S T).complementDimensions) Complex
        (splitComplementBACLabel S T hST labels).2) := by sorry
