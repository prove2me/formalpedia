-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_doubleInteractionCoefficient_commutes_leftIsotypicSector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.doubleInteractionCoefficient_commutes_leftIsotypicSector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:21:08.484327+00:00
-- url     : https://prove2.me/theorems/95d9b0d9-2939-4a34-a7e6-d82009a34893
-- title:
--   BPTCommuting Projector Model: double Interaction Coefficient commutes left Isotypic Sector
-- statement:
--   Taking a right and then left interaction coefficient preserves commutation
--   with a lifted left-isotypic sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4064-L4108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4064-L4108

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.doubleInteractionCoefficient_commutes_leftIsotypicSector
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    (c c' : C) (a a' : A) :
    Commute
      (leftInteractionCoefficient
        (rightInteractionCoefficient
          (overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q) c c') a a')
      (leftIsotypicSectorProjector P component) := by sorry
