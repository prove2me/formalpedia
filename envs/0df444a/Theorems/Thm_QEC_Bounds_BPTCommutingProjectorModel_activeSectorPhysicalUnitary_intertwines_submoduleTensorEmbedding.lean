-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_activeSectorPhysicalUnitary_intertwines_submoduleTensorEmbedding
-- name    : QEC.Bounds.BPTCommutingProjectorModel.activeSectorPhysicalUnitary_intertwines_submoduleTensorEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:25:07.150252+00:00
-- url     : https://prove2.me/theorems/b1c23104-c099-477e-b8da-04c49a01a9c9
-- title:
--   BPTCommuting Projector Model: active Sector Physical Unitary intertwines submodule Tensor Embedding
-- statement:
--   The physical active-sector extension has exactly the prescribed action on the
--   joint subtype embedding.  Its unconstrained orthogonal complement never
--   enters this equality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L50-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L50-L68

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.activeSectorPhysicalUnitary_intertwines_submoduleTensorEmbedding
    {B C WB NB WC NC : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup WB] [InnerProductSpace Complex WB] [Semantics.FiniteQuantumSystem WB]
    [NormedAddCommGroup NB] [InnerProductSpace Complex NB] [Semantics.FiniteQuantumSystem NB]
    [NormedAddCommGroup WC] [InnerProductSpace Complex WC] [Semantics.FiniteQuantumSystem WC]
    [NormedAddCommGroup NC] [InnerProductSpace Complex NC] [Semantics.FiniteQuantumSystem NC]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    (activeSectorPhysicalUnitary pB pC UB UC U).toLinearEquiv.toLinearMap.comp
        (submoduleTensorEmbedding pB pC).toLinearMap =
      (submoduleTensorEmbedding pB pC).toLinearMap.comp
        (activeSectorJointBCUnitary pB pC UB UC U).toLinearEquiv.toLinearMap := by sorry
