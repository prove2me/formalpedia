-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_commute_leftOverlap_of_commute_leftInteractionCoefficients
-- name    : QEC.Bounds.BPTCommutingProjectorModel.commute_leftOverlap_of_commute_leftInteractionCoefficients
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:06:55.210063+00:00
-- url     : https://prove2.me/theorems/5b08aa23-2621-4c26-8583-9fe041443d67
-- title:
--   BPTCommuting Projector Model: commute left Overlap of commute left Interaction Coefficients
-- statement:
--   Commuting with every left interaction coefficient is equivalent to commuting
--   with the full left overlap operator after lifting the overlap operator by the
--   identity on the exterior factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2064-L2077
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2064-L2077

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

theorem QEC.Bounds.BPTCommutingProjectorModel.commute_leftOverlap_of_commute_leftInteractionCoefficients
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) (Z : Semantics.Operator B)
    (hcommute : ∀ a a' : A, Commute Z (leftInteractionCoefficient P a a')) :
    Commute P (TensorProduct.map (1 : Semantics.Operator A) Z) := by sorry
