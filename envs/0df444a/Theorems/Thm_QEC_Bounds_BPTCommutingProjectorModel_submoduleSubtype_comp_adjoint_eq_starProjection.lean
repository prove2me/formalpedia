-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_submoduleSubtype_comp_adjoint_eq_starProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.submoduleSubtype_comp_adjoint_eq_starProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:18:59.736092+00:00
-- url     : https://prove2.me/theorems/77c7afb9-6f24-4cfc-9ae7-2b5ab21b2b7c
-- title:
--   BPTCommuting Projector Model: submodule Subtype comp adjoint eq star Projection
-- statement:
--   The inclusion followed by its adjoint is the orthogonal sector projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L51-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L51-L72

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

theorem QEC.Bounds.BPTCommutingProjectorModel.submoduleSubtype_comp_adjoint_eq_starProjection
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (p : Submodule Complex H) :
    p.subtype.comp (LinearMap.adjoint p.subtype) = p.starProjection.toLinearMap := by sorry
