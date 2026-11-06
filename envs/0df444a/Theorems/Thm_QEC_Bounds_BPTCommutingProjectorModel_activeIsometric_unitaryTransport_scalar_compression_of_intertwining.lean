-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_activeIsometric_unitaryTransport_scalar_compression_of_intertwining
-- name    : QEC.Bounds.BPTCommutingProjectorModel.activeIsometric_unitaryTransport_scalar_compression_of_intertwining
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:58:01.606019+00:00
-- url     : https://prove2.me/theorems/3ab495ee-31a4-4b4c-a8c3-e42ec4643a93
-- title:
--   BPTCommuting Projector Model: active Isometric unitary Transport scalar compression of intertwining
-- statement:
--   Scalar compression survives an active isometric-sector compression and a
--   subsequent unitary coordinate transport.  The active support is derived from
--   the ambient orthogonal projection; it is not a scalar-compression hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Core.lean#L52-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Core.lean#L52-L79

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Data
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Core
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000

theorem QEC.Bounds.BPTCommutingProjectorModel.activeIsometric_unitaryTransport_scalar_compression_of_intertwining
    {H K K' : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup K'] [InnerProductSpace Complex K']
    [Semantics.FiniteQuantumSystem K']
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (Q R : Semantics.Operator K) (Rsub : Semantics.Operator H)
    (T : Semantics.UnitaryTransport H K') (scalar : Complex)
    (hJadj_eq : LinearMap.adjoint J = Jadj)
    (hQ : Q.IsSymmetricProjection)
    (hright : Q.comp (J.comp Jadj) = Q)
    (hscalar : Q * R * Q = scalar • Q)
    (hintertwines : J.comp Rsub = R.comp J) :
    T.conjOperator (Jadj.comp (Q.comp J)) * T.conjOperator Rsub *
        T.conjOperator (Jadj.comp (Q.comp J)) =
      scalar • T.conjOperator (Jadj.comp (Q.comp J)) := by sorry
