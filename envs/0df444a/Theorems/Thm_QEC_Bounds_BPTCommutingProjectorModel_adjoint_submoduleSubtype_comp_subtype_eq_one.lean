-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_submoduleSubtype_comp_subtype_eq_one
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_submoduleSubtype_comp_subtype_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:19:04.621755+00:00
-- url     : https://prove2.me/theorems/0779f1bb-ca13-4d3a-85b6-d5c5788ed091
-- title:
--   BPTCommuting Projector Model: adjoint submodule Subtype comp subtype eq one
-- statement:
--   The adjoint of a finite-dimensional subspace inclusion is a left inverse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L41-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L41-L48

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

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_submoduleSubtype_comp_subtype_eq_one
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (p : Submodule Complex H) :
    (LinearMap.adjoint p.subtype).comp p.subtype = (1 : Semantics.Operator p) := by sorry
