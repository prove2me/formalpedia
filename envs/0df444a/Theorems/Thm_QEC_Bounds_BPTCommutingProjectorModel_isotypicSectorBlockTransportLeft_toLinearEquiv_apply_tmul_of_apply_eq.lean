-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:35:15.667043+00:00
-- url     : https://prove2.me/theorems/076848b7-05f2-4888-ae48-cc58993c9c1e
-- title:
--   BPTCommuting Projector Model: isotypic Sector Block Transport Left to Linear Equiv apply tmul of apply eq
-- statement:
--   The linear-equivalence view of the preceding tensor-generator transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/Coherence.lean#L45-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/Coherence.lean#L45-L58

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Coherence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (a : A) (h : H) (c : C) (w : W) (n : N)
    (hU : U.toLinearEquiv h = w ⊗ₜ[Complex] n) :
    (isotypicSectorBlockTransportLeft A H W N C U).toLinearEquiv
        ((a ⊗ₜ[Complex] h) ⊗ₜ[Complex] c) =
      (a ⊗ₜ[Complex] w) ⊗ₜ[Complex] (n ⊗ₜ[Complex] c) := by sorry
