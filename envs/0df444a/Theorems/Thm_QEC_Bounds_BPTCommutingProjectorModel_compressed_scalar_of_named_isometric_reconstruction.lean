-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compressed_scalar_of_named_isometric_reconstruction
-- name    : QEC.Bounds.BPTCommutingProjectorModel.compressed_scalar_of_named_isometric_reconstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:29.975315+00:00
-- url     : https://prove2.me/theorems/a259097f-0207-4538-9273-9cfec2b1a24b
-- title:
--   BPTCommuting Projector Model: compressed scalar of named isometric reconstruction
-- statement:
--   An isometric reconstruction can expose a named compressed block without
--   repeating its `J† R J` expression in every downstream physical statement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ScalarTransport.lean#L136-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ScalarTransport.lean#L136-L169

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ProjectionBlock
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ScalarTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.compressed_scalar_of_named_isometric_reconstruction
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (R L : Semantics.Operator K)
    (Rsub Lsub : Semantics.Operator H) (scalar : Complex)
    (hJadj : (LinearMap.adjoint J).comp J = (1 : Semantics.Operator H))
    (hreconstruct : R = J.comp (Rsub.comp (LinearMap.adjoint J)))
    (hprobe : (LinearMap.adjoint J).comp (L.comp J) = Lsub)
    (hscalar : R * L * R = scalar • R) :
    Rsub * Lsub * Rsub = scalar • Rsub := by sorry
