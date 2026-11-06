-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftInteractionCoefficient_rightTensorExtensionAfterLeft
-- name    : QEC.Bounds.BPTCommutingProjectorModel.leftInteractionCoefficient_rightTensorExtensionAfterLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:23:23.106138+00:00
-- url     : https://prove2.me/theorems/442a57ba-df22-428a-81fc-05a20e174f20
-- title:
--   BPTCommuting Projector Model: left Interaction Coefficient right Tensor Extension After Left
-- statement:
--   The `A`-coefficients of a left block extended by an inert right tensor factor
--   are exactly the original coefficients tensored with the identity.  This is the
--   operator-level form of the source notation `Pi_{AB'} tensor 1_{B''}`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1329-L1375
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1329-L1375

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

theorem QEC.Bounds.BPTCommutingProjectorModel.leftInteractionCoefficient_rightTensorExtensionAfterLeft
    (A W N : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (T : Semantics.Operator (Semantics.CompositeSystem A W)) (a a' : A) :
    leftInteractionCoefficient (rightTensorExtensionAfterLeft A W N T) a a' =
      TensorProduct.map (leftInteractionCoefficient T a a')
        (1 : Semantics.Operator N) := by sorry
