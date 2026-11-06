-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftIsotypicSectorProjector_commute_leftInteractionCoefficient
-- name    : QEC.Bounds.BPTCommutingProjectorModel.leftIsotypicSectorProjector_commute_leftInteractionCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:01:27.741775+00:00
-- url     : https://prove2.me/theorems/b60b536c-1b72-4165-8143-3e435d3e3702
-- title:
--   BPTCommuting Projector Model: left Isotypic Sector Projector commute left Interaction Coefficient
-- statement:
--   A left-interaction sector commutes with every displayed left coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4932-L4949
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4932-L4949

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

theorem QEC.Bounds.BPTCommutingProjectorModel.leftIsotypicSectorProjector_commute_leftInteractionCoefficient
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (a a' : A) :
    Commute (leftIsotypicSectorProjector P component)
      (leftInteractionCoefficient P a a') := by sorry
