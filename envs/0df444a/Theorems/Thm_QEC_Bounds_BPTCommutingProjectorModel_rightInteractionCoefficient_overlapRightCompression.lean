-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightInteractionCoefficient_overlapRightCompression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.rightInteractionCoefficient_overlapRightCompression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:25:14.618283+00:00
-- url     : https://prove2.me/theorems/ffa31f64-6680-483c-990b-2ae06bd106a2
-- title:
--   BPTCommuting Projector Model: right Interaction Coefficient overlap Right Compression
-- statement:
--   Right interaction coefficients commute with Hilbert-space compression.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3194-L3218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3194-L3218

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

theorem QEC.Bounds.BPTCommutingProjectorModel.rightInteractionCoefficient_overlapRightCompression
    {H B C : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) (inclusion : H →ₗ[Complex] B)
    (c c' : C) :
    rightInteractionCoefficient (overlapRightCompression Q inclusion) c c' =
      (LinearMap.adjoint inclusion).comp
        ((rightInteractionCoefficient Q c c').comp inclusion) := by sorry
