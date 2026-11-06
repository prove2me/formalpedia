-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_pureFactorTensorComplementProjector_eq_rankOne_mul_complementExtension
-- name    : QEC.Bounds.BPTCommutingProjectorModel.pureFactorTensorComplementProjector_eq_rankOne_mul_complementExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:44:23.70732+00:00
-- url     : https://prove2.me/theorems/1120e126-01d6-4fdd-a076-c6a567655abb
-- title:
--   BPTCommuting Projector Model: pure Factor Tensor Complement Projector eq rank One mul complement Extension
-- statement:
--   The target pure-factor operator is literally a selected rank-one extension
--   times its true complement operator.  This is the final D5 endpoint shape.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L5268-L5282
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L5268-L5282

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.pureFactorTensorComplementProjector_eq_rankOne_mul_complementExtension
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (phi : (M.regionSubsystem region).selectedSystem)
    (complementProjector : Semantics.Operator (M.regionSubsystem region).complementSystem) :
    M.pureFactorTensorComplementProjector region phi complementProjector =
      (M.regionSubsystem region).extendLocalToRegister
        (InnerProductSpace.rankOne Complex phi phi).toLinearMap *
      ((M.regionSubsystem region).registerFactorization.symm.conjOperator
        (TensorProduct.map
          (1 : Semantics.Operator (M.regionSubsystem region).selectedSystem)
          complementProjector)) := by sorry
