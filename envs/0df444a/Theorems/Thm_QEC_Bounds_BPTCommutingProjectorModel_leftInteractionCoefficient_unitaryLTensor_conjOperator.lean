-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftInteractionCoefficient_unitaryLTensor_conjOperator
-- name    : QEC.Bounds.BPTCommutingProjectorModel.leftInteractionCoefficient_unitaryLTensor_conjOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:04:08.932843+00:00
-- url     : https://prove2.me/theorems/f07b3dc9-bd6b-4bd3-a2ad-a5b7afb84517
-- title:
--   BPTCommuting Projector Model: left Interaction Coefficient unitary LTensor conj Operator
-- statement:
--   Left interaction coefficients commute with tensoring a unitary transport on
--   the overlap factor.  It transports the coefficient by the same unitary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1291-L1322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1291-L1322

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

theorem QEC.Bounds.BPTCommutingProjectorModel.leftInteractionCoefficient_unitaryLTensor_conjOperator
    {A H K : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K)
    (T : Semantics.Operator (Semantics.CompositeSystem A H)) (a a' : A) :
    leftInteractionCoefficient ((unitaryLTensor A U).conjOperator T) a a' =
      U.conjOperator (leftInteractionCoefficient T a a') := by sorry
