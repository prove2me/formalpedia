-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_unique_active_leftIsotypicSector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exists_unique_active_leftIsotypicSector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:09:51.155843+00:00
-- url     : https://prove2.me/theorems/f48ffc19-c9e5-4bf6-81dc-94bf81eadfa6
-- title:
--   BPTCommuting Projector Model: exists unique active left Isotypic Sector
-- statement:
--   Finite sector-collapse for the interaction-algebra decomposition.  If every
--   local sector is either absent from a nonzero projector or contains its entire
--   range, then exactly one isotypic sector is active.  The two hypotheses are
--   supplied later by external-boundary no-information and the proved local
--   commutation of `leftIsotypicSectorProjector`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L5020-L5103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L5020-L5103

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

theorem QEC.Bounds.BPTCommutingProjectorModel.exists_unique_active_leftIsotypicSector
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) (F : Semantics.Operator B)
    (hF : F ≠ 0)
    (hcommute : ∀ component : isotypicComponents (leftInteractionAlgebra P) B,
      Commute F (leftIsotypicSectorProjector P component))
    (hsector : ∀ component : isotypicComponents (leftInteractionAlgebra P) B,
      F * leftIsotypicSectorProjector P component = 0 ∨
        F * leftIsotypicSectorProjector P component = F) :
    ∃ component : isotypicComponents (leftInteractionAlgebra P) B,
      F * leftIsotypicSectorProjector P component = F ∧
        ∀ other : isotypicComponents (leftInteractionAlgebra P) B, other ≠ component →
          F * leftIsotypicSectorProjector P other = 0 := by sorry
