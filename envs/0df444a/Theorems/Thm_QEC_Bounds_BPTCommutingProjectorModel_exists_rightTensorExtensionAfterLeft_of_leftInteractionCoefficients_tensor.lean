-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_rightTensorExtensionAfterLeft_of_leftInteractionCoefficients_tensor
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exists_rightTensorExtensionAfterLeft_of_leftInteractionCoefficients_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:23:44.378805+00:00
-- url     : https://prove2.me/theorems/ac6a6b72-e37c-4c06-9a3d-f1eb6a6b8443
-- title:
--   BPTCommuting Projector Model: exists right Tensor Extension After Left of left Interaction Coefficients tensor
-- statement:
--   BV03 left-block reconstruction.  If every left interaction coefficient of an
--   operator on `A tensor (W tensor N)` is an operator on `W` tensored with the
--   identity on `N`, then contracting a unit vector of `N` constructs the unique
--   left block and recovers the full operator as that block tensored with `1_N`.
--   This is the first operator equality behind the source tensor-block
--   factorization, rather than a statement only about its coefficient algebra.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1662-L1684
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1662-L1684

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

theorem QEC.Bounds.BPTCommutingProjectorModel.exists_rightTensorExtensionAfterLeft_of_leftInteractionCoefficients_tensor
    (A W N : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (T : Semantics.Operator (Semantics.CompositeSystem A (Semantics.CompositeSystem W N)))
    (eta : N) (heta : ‖eta‖ = 1)
    (hcoefficients : ∀ a a' : A, ∃ R : Semantics.Operator W,
      leftInteractionCoefficient T a a' =
        TensorProduct.map R (1 : Semantics.Operator N)) :
    ∃ Tleft : Semantics.Operator (Semantics.CompositeSystem A W),
      T = rightTensorExtensionAfterLeft A W N Tleft := by sorry
