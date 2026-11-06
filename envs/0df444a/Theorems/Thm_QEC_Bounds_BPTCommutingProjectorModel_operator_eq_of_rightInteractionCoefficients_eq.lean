-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_operator_eq_of_rightInteractionCoefficients_eq
-- name    : QEC.Bounds.BPTCommutingProjectorModel.operator_eq_of_rightInteractionCoefficients_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:01:03.402321+00:00
-- url     : https://prove2.me/theorems/7b28a07f-f87a-4d23-a2fc-d7652ad789fe
-- title:
--   BPTCommuting Projector Model: operator eq of right Interaction Coefficients eq
-- statement:
--   Right interaction coefficients also determine an overlap operator.  This is
--   the `B tensor C` counterpart of left-coefficient reconstruction and is used to
--   turn a reducing interaction sector into commutation with the actual right
--   projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1919-L1971
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1919-L1971

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

theorem QEC.Bounds.BPTCommutingProjectorModel.operator_eq_of_rightInteractionCoefficients_eq
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hcoefficients : ∀ c c' : C,
      rightInteractionCoefficient P c c' = rightInteractionCoefficient Q c c') :
    P = Q := by sorry
