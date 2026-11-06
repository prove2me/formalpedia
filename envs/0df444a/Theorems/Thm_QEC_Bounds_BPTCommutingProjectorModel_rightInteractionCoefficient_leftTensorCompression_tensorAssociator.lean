-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightInteractionCoefficient_leftTensorCompression_tensorAssociator
-- name    : QEC.Bounds.BPTCommutingProjectorModel.rightInteractionCoefficient_leftTensorCompression_tensorAssociator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:24:23.061785+00:00
-- url     : https://prove2.me/theorems/35d44295-f779-4acd-b05f-76916a4750d4
-- title:
--   BPTCommuting Projector Model: right Interaction Coefficient left Tensor Compression tensor Associator
-- statement:
--   Right coefficients commute with left-factor compression after reassociation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1859-L1911
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1859-L1911

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

theorem QEC.Bounds.BPTCommutingProjectorModel.rightInteractionCoefficient_leftTensorCompression_tensorAssociator
    (W N C : Type u)
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (T : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem W N) C))
    (eta : W) (c c' : C) :
    rightInteractionCoefficient
      (leftTensorCompression eta ((tensorAssociatorUnitary W N C).conjOperator T)) c c' =
      leftTensorCompression eta (rightInteractionCoefficient T c c') := by sorry
