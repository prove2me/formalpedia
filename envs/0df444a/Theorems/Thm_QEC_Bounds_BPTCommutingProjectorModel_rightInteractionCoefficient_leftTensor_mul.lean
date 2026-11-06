-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightInteractionCoefficient_leftTensor_mul
-- name    : QEC.Bounds.BPTCommutingProjectorModel.rightInteractionCoefficient_leftTensor_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:24:23.896021+00:00
-- url     : https://prove2.me/theorems/8a89d11a-4f23-45c8-b603-6ff2c9d8c4d3
-- title:
--   BPTCommuting Projector Model: right Interaction Coefficient left Tensor mul
-- statement:
--   A left tensor extension is pulled through a right interaction coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2031-L2043
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2031-L2043

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

theorem QEC.Bounds.BPTCommutingProjectorModel.rightInteractionCoefficient_leftTensor_mul
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (Z : Semantics.Operator B) (c c' : C) :
    rightInteractionCoefficient (TensorProduct.map Z (1 : Semantics.Operator C) * Q) c c' =
      Z * rightInteractionCoefficient Q c c' := by sorry
