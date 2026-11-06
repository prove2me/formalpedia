-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypic_compression_overlap_product_eq_sector_block_product
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypic_compression_overlap_product_eq_sector_block_product
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:29:32.621203+00:00
-- url     : https://prove2.me/theorems/4f0b956f-9b2b-4a61-b217-63e0e3b5c358
-- title:
--   BPTCommuting Projector Model: isotypic compression overlap product eq sector block product
-- statement:
--   The compression of a commuting overlap product to one left-isotypic sector is
--   the product of its two concrete sector blocks.  Sector invariance of the right
--   overlap factor supplies the inserted `J J†`; this is the operator equality
--   that turns the BV03 coefficient block theorem into a physical block product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L524-L665
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L524-L665

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypic_compression_overlap_product_eq_sector_block_product
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C)
      (component.1.restrictScalars Complex))).comp
        (((overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q).comp
          (tensorTripleSubtypeEmbedding (A := A) (C := C)
            (component.1.restrictScalars Complex)))) =
      overlapLiftLeft (C := C) (overlapProjectorOnIsotypicComponent P component) *
        overlapLiftRight (A := A)
          (overlapRightProjectorOnIsotypicComponent P Q component) := by sorry
