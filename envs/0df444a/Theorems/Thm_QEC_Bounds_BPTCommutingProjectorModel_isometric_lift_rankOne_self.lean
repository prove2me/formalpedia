-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isometric_lift_rankOne_self
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isometric_lift_rankOne_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:11:12.811214+00:00
-- url     : https://prove2.me/theorems/53a837b4-65fa-4c9c-b8d9-69b987538584
-- title:
--   BPTCommuting Projector Model: isometric lift rank One self
-- statement:
--   Lifting a rank-one self-projector along an isometric embedding is rank one at the image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L603-L615
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L603-L615

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isometric_lift_rankOne_self
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K)
    (hJ : (LinearMap.adjoint J).comp J = (1 : Semantics.Operator H))
    (v : H) :
    J.comp ((InnerProductSpace.rankOne Complex v v).toLinearMap.comp
      (LinearMap.adjoint J)) =
      (InnerProductSpace.rankOne Complex (J v) (J v)).toLinearMap := by sorry
