-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_commute_rightOverlap_of_commute_rightInteractionCoefficients
-- name    : QEC.Bounds.BPTCommutingProjectorModel.commute_rightOverlap_of_commute_rightInteractionCoefficients
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:24:31.402419+00:00
-- url     : https://prove2.me/theorems/a7dced15-ac9b-4a9f-a5b3-8e4e27f0bab7
-- title:
--   BPTCommuting Projector Model: commute right Overlap of commute right Interaction Coefficients
-- statement:
--   Commuting with every right interaction coefficient is equivalent to commuting
--   with the full right overlap operator after lifting the overlap operator by the
--   identity on the exterior factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2084-L2097
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2084-L2097

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

theorem QEC.Bounds.BPTCommutingProjectorModel.commute_rightOverlap_of_commute_rightInteractionCoefficients
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) (Z : Semantics.Operator B)
    (hcommute : ∀ c c' : C, Commute Z (rightInteractionCoefficient Q c c')) :
    Commute Q (TensorProduct.map Z (1 : Semantics.Operator C)) := by sorry
