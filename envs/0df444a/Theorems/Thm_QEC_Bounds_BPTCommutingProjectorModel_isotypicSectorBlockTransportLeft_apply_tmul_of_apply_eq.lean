-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_apply_tmul_of_apply_eq
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_apply_tmul_of_apply_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:35:04.583308+00:00
-- url     : https://prove2.me/theorems/0b8d8cb8-cc20-428c-b526-4884b5bb848b
-- title:
--   BPTCommuting Projector Model: isotypic Sector Block Transport Left apply tmul of apply eq
-- statement:
--   The sequential B/C coordinate comparison is checked on literal tensor
--   generators.  This small pointwise form keeps the two sector transports
--   available for later reassociation proofs without hiding a tensor-coordinate
--   assumption in the common-factor assembly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/Coherence.lean#L29-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/Coherence.lean#L29-L42

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_apply_tmul_of_apply_eq
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (a : A) (h : H) (c : C) (w : W) (n : N)
    (hU : U h = w ⊗ₜ[Complex] n) :
    isotypicSectorBlockTransportLeft A H W N C U ((a ⊗ₜ[Complex] h) ⊗ₜ[Complex] c) =
      (a ⊗ₜ[Complex] w) ⊗ₜ[Complex] (n ⊗ₜ[Complex] c) := by sorry
