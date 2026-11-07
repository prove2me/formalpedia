-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_conj_scalar_compression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conj_scalar_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:11:14.662604+00:00
-- url     : https://prove2.me/theorems/2b0699b8-494e-4288-ac5a-58c569b4e5d5
-- title:
--   BPTCommuting Projector Model: unitary Transport conj scalar compression
-- statement:
--   Unitary coordinates preserve a scalar compression equation.  This is the last
--   generic transport used after the active isometric-sector compression below.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Core.lean#L29-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Core.lean#L29-L45

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

theorem QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conj_scalar_compression
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (Q R : Semantics.Operator H)
    (scalar : Complex) (hscalar : Q * R * Q = scalar • Q) :
    U.conjOperator Q * U.conjOperator R * U.conjOperator Q =
      scalar • U.conjOperator Q := by sorry
