-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftInteractionCoefficient_overlapProjectorOnIsotypicComponent
-- name    : QEC.Bounds.BPTCommutingProjectorModel.leftInteractionCoefficient_overlapProjectorOnIsotypicComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:25:28.858269+00:00
-- url     : https://prove2.me/theorems/811a2582-6860-41e5-8304-828a7d12c8f5
-- title:
--   BPTCommuting Projector Model: left Interaction Coefficient overlap Projector On Isotypic Component
-- statement:
--   The compressed overlap block has precisely the restricted left interaction
--   coefficient.  This turns the source interaction algebra into an equality of
--   actual block operators, which the unitary tensor coordinates reconstruct
--   below.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3236-L3298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3236-L3298

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

theorem QEC.Bounds.BPTCommutingProjectorModel.leftInteractionCoefficient_overlapProjectorOnIsotypicComponent
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (a a' : A) :
    leftInteractionCoefficient (overlapProjectorOnIsotypicComponent P component) a a' =
      isotypicLeftAction (leftInteractionAlgebra P) component
        ⟨leftInteractionCoefficient P a a',
          leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩ := by sorry
