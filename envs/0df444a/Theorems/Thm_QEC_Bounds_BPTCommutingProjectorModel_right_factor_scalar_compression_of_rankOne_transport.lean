-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_right_factor_scalar_compression_of_rankOne_transport
-- name    : QEC.Bounds.BPTCommutingProjectorModel.right_factor_scalar_compression_of_rankOne_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:55:51.269714+00:00
-- url     : https://prove2.me/theorems/9646ee9f-39d6-4dbc-9e34-4a3c9dca90fc
-- title:
--   BPTCommuting Projector Model: right factor scalar compression of rank One transport
-- statement:
--   After a unitary block transport exposes a normalized rank-one left factor, a
--   scalar compression relation descends to the right tensor factor.  Keeping this
--   step independent of the BPT coordinate types prevents their definitions from
--   being unfolded during tensor cancellation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/RankOneTransport.lean#L27-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/RankOneTransport.lean#L27-L75

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RightProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RankOneTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped ComplexOrder TensorProduct
universe u
open QEC.Bounds.BPTCommutingProjectorModel

theorem QEC.Bounds.BPTCommutingProjectorModel.right_factor_scalar_compression_of_rankOne_transport
    {H A B : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B]
    (T : Semantics.UnitaryTransport H (Semantics.CompositeSystem A B))
    (R L : Semantics.Operator H) (phi : A) (hphi : ‖phi‖ = 1)
    (Q X : Semantics.Operator B) (scalar : Complex)
    (hR : T.conjOperator R =
      TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Q)
    (hL : T.conjOperator L =
      TensorProduct.map (1 : Semantics.Operator A) X)
    (hscalar : R * L * R = scalar • R) :
    Q * X * Q = scalar • Q := by sorry
