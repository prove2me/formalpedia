-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_complementABCFactorization_apply_basis
-- name    : QEC.Bounds.BPTEntropy.QuditSubsystem.complementABCFactorization_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:47:49.829379+00:00
-- url     : https://prove2.me/theorems/fd2949fd-8703-4f35-aa71-d4260f5ad500
-- title:
--   Qudit Subsystem: complement ABCFactorization apply basis
-- statement:
--   The Qudit Subsystem construction uses the complement ABCFactorization apply basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1082-L1094
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1082-L1094

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

theorem QEC.Bounds.BPTEntropy.QuditSubsystem.complementABCFactorization_apply_basis (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label S.complementDimensions) :
    complementABCFactorization S T hST
      (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex labels) =
      (EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
        (splitComplementABCLabel S T hST labels).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun
        (Qudit.Label (unionSubsystem S T).complementDimensions) Complex
        (splitComplementABCLabel S T hST labels).2) := by sorry
