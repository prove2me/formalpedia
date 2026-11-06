-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_leftTensorExtensionBeforeRight_of_rightInteractionCoefficients_tensor
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exists_leftTensorExtensionBeforeRight_of_rightInteractionCoefficients_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:24:12.689068+00:00
-- url     : https://prove2.me/theorems/3759cf4d-a956-41ed-9e42-89dd26528add
-- title:
--   BPTCommuting Projector Model: exists left Tensor Extension Before Right of right Interaction Coefficients tensor
-- statement:
--   BV03 right-block reconstruction.  Right coefficients which are identity on the
--   simple factor determine an actual `1_W tensor T_right` overlap operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1977-L1999
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1977-L1999

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

theorem QEC.Bounds.BPTCommutingProjectorModel.exists_leftTensorExtensionBeforeRight_of_rightInteractionCoefficients_tensor
    (W N C : Type u)
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (T : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem W N) C))
    (eta : W) (heta : ‖eta‖ = 1)
    (hcoefficients : ∀ c c' : C, ∃ R : Semantics.Operator N,
      rightInteractionCoefficient T c c' =
        TensorProduct.map (1 : Semantics.Operator W) R) :
    ∃ Tright : Semantics.Operator (Semantics.CompositeSystem N C),
      T = leftTensorExtensionBeforeRight W N C Tright := by sorry
