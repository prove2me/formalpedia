-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftInteractionCoefficient_mul_rightTensor
-- name    : QEC.Bounds.BPTCommutingProjectorModel.leftInteractionCoefficient_mul_rightTensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:49:40.15537+00:00
-- url     : https://prove2.me/theorems/754100c8-4821-45c0-a075-957b3af483fd
-- title:
--   BPTCommuting Projector Model: left Interaction Coefficient mul right Tensor
-- statement:
--   A right tensor extension is pulled through a left interaction coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2002-L2013
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2002-L2013

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

theorem QEC.Bounds.BPTCommutingProjectorModel.leftInteractionCoefficient_mul_rightTensor
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Z : Semantics.Operator B) (a a' : A) :
    leftInteractionCoefficient (P * TensorProduct.map (1 : Semantics.Operator A) Z) a a' =
      leftInteractionCoefficient P a a' * Z := by sorry
