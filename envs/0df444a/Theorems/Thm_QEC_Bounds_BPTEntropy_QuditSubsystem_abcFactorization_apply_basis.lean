-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_abcFactorization_apply_basis
-- name    : QEC.Bounds.BPTEntropy.QuditSubsystem.abcFactorization_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:48:06.951278+00:00
-- url     : https://prove2.me/theorems/cff5c5f5-f4af-4f71-a1f7-040eae7ed49c
-- title:
--   Qudit Subsystem: abc Factorization apply basis
-- statement:
--   Computational-basis action of the explicit `A`/`B`/`C` factorization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L999-L1013
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L999-L1013

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

theorem QEC.Bounds.BPTEntropy.QuditSubsystem.abcFactorization_apply_basis (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label q) :
    abcFactorization S T hST (EuclideanSpace.basisFun (Qudit.Label q) Complex labels) =
      (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
        (splitABCLabel S T labels).1) ⊗ₜ[Complex]
      ((EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
        (splitABCLabel S T labels).2.1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun
        (Qudit.Label (unionSubsystem S T).complementDimensions) Complex
        (splitABCLabel S T labels).2.2)) := by sorry
