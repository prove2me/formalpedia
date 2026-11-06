-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_conjOperator_compression_of_intertwining
-- name    : QEC.Bounds.BPTCommutingProjectorModel.conjOperator_compression_of_intertwining
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:24:52.968207+00:00
-- url     : https://prove2.me/theorems/37b987f6-f189-4c03-876c-67f9d4b81056
-- title:
--   BPTCommuting Projector Model: conj Operator compression of intertwining
-- statement:
--   Compression after ambient unitary conjugation is conjugation of the compressed
--   operator whenever the unitary intertwines the embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L423-L461
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L423-L461

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Core
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.conjOperator_compression_of_intertwining
    {S H : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (J : S →ₗ[Complex] H)
    (F : Semantics.UnitaryTransport H H) (W : Semantics.UnitaryTransport S S)
    (hintertwines : F.toLinearEquiv.toLinearMap.comp J = J.comp W.toLinearEquiv.toLinearMap)
    (P : Semantics.Operator H) :
    (LinearMap.adjoint J).comp ((F.conjOperator P).comp J) =
      W.conjOperator ((LinearMap.adjoint J).comp (P.comp J)) := by sorry
