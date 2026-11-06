-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightInteractionCoefficient_unitaryRTensor_conjOperator
-- name    : QEC.Bounds.BPTCommutingProjectorModel.rightInteractionCoefficient_unitaryRTensor_conjOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:23:19.597561+00:00
-- url     : https://prove2.me/theorems/12b41d15-37cc-4393-91f0-00e907d51be6
-- title:
--   BPTCommuting Projector Model: right Interaction Coefficient unitary RTensor conj Operator
-- statement:
--   Right interaction coefficients commute with a unitary transport on the overlap factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1510-L1541
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1510-L1541

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

theorem QEC.Bounds.BPTCommutingProjectorModel.rightInteractionCoefficient_unitaryRTensor_conjOperator
    {H K C : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H K)
    (T : Semantics.Operator (Semantics.CompositeSystem H C)) (c c' : C) :
    rightInteractionCoefficient ((unitaryRTensor U C).conjOperator T) c c' =
      U.conjOperator (rightInteractionCoefficient T c c') := by sorry
