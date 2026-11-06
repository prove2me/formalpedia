-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_doubleInteractionCoefficient_overlap_product_eq
-- name    : QEC.Bounds.BPTCommutingProjectorModel.doubleInteractionCoefficient_overlap_product_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:26:47.477204+00:00
-- url     : https://prove2.me/theorems/8c9ac385-c651-4ce4-a22c-54c58649b62f
-- title:
--   BPTCommuting Projector Model: double Interaction Coefficient overlap product eq
-- statement:
--   The double matrix element of an actual overlapping product is the product of
--   its left and right interaction coefficients.  This is the coefficient-level
--   form of the BV03 overlap relation used to transfer sector commutation to the
--   nonzero coefficient that witnesses an active code sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4044-L4058
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4044-L4058

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

theorem QEC.Bounds.BPTCommutingProjectorModel.doubleInteractionCoefficient_overlap_product_eq
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a a' : A) (c c' : C) :
    leftInteractionCoefficient
        (rightInteractionCoefficient
          (overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q) c c') a a' =
      leftInteractionCoefficient P a a' * rightInteractionCoefficient Q c c' := by sorry
