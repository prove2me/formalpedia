-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlap_product_commutes_leftIsotypicSectorLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.overlap_product_commutes_leftIsotypicSectorLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:16:31.282758+00:00
-- url     : https://prove2.me/theorems/2f660cc5-9862-45e0-b67b-d0d49f4b0f82
-- title:
--   BPTCommuting Projector Model: overlap product commutes left Isotypic Sector Lift
-- statement:
--   The product of a commuting overlap pair commutes with the lifted projector
--   onto every left-isotypic sector.  This is the coefficient-free commutation
--   input needed to instantiate finite sector collapse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3968-L4036
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3968-L4036

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

theorem QEC.Bounds.BPTCommutingProjectorModel.overlap_product_commutes_leftIsotypicSectorLift
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    Commute
      (overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q)
      (overlapLiftLeft (C := C)
        (TensorProduct.map (1 : Semantics.Operator A)
          (leftIsotypicSectorProjector P component))) := by sorry
