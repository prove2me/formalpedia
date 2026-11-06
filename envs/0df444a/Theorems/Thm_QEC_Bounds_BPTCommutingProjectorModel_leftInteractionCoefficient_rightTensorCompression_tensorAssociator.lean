-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftInteractionCoefficient_rightTensorCompression_tensorAssociator
-- name    : QEC.Bounds.BPTCommutingProjectorModel.leftInteractionCoefficient_rightTensorCompression_tensorAssociator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:23:22.085266+00:00
-- url     : https://prove2.me/theorems/7701cc22-fff4-441d-8a38-85473daaf3f3
-- title:
--   BPTCommuting Projector Model: left Interaction Coefficient right Tensor Compression tensor Associator
-- statement:
--   Taking a left interaction coefficient commutes with contracting the inert
--   factor after reassociation.  This identifies the coefficient of the recovered
--   left block with the normalized contraction of the displayed `L tensor 1`
--   coefficient, which is the key reconstruction step in the BV03 block proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1383-L1434
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1383-L1434

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

theorem QEC.Bounds.BPTCommutingProjectorModel.leftInteractionCoefficient_rightTensorCompression_tensorAssociator
    (A W N : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (T : Semantics.Operator (Semantics.CompositeSystem A (Semantics.CompositeSystem W N)))
    (eta : N) (a a' : A) :
    leftInteractionCoefficient
      (rightTensorCompression eta ((tensorAssociatorUnitary A W N).symm.conjOperator T)) a a' =
      rightTensorCompression eta (leftInteractionCoefficient T a a') := by sorry
