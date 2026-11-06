-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorTripleSubtypeEmbedding_comp_adjoint_eq_sectorLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorTripleSubtypeEmbedding_comp_adjoint_eq_sectorLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:28:37.726196+00:00
-- url     : https://prove2.me/theorems/5594542f-1ba8-4827-9a87-6fe705032d7c
-- title:
--   BPTCommuting Projector Model: tensor Triple Subtype Embedding comp adjoint eq sector Lift
-- statement:
--   Returning from a subspace coordinate by its adjoint gives the literal tensor
--   extension of that subspace's orthogonal projector.  This is the second half
--   of the active-block reconstruction and is used to turn `Pi * sector = Pi`
--   into an equality with the compressed BV03 block product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L112-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L112-L133

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

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorTripleSubtypeEmbedding_comp_adjoint_eq_sectorLift
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (p : Submodule Complex B) :
    (tensorTripleSubtypeEmbedding (A := A) (C := C) p).comp
      (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C) p)) =
        TensorProduct.map
          (TensorProduct.map (1 : Semantics.Operator A) p.starProjection.toLinearMap)
          (1 : Semantics.Operator C) := by sorry
