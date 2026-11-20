-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_partialTraceRightRaw_tensorMap
-- name    : QEC.Bounds.BPTCommutingProjectorModel.partialTraceRightRaw_tensorMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:32:33.169279+00:00
-- url     : https://prove2.me/theorems/a3c05f21-d2cb-49ae-819b-7a9b6c481875
-- title:
--   BPTCommuting Projector Model: partial Trace Right Raw tensor Map
-- statement:
--   Tracing the right factor of an operator tensor product multiplies by its trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean#L383-L411
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean#L383-L411

import Definitions.Def_QEC_Bounds_BPTDisentangling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open Semantics
open Semantics.DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.partialTraceRightRaw_tensorMap (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator H) (B : Operator K) :
    partialTraceRightRaw H K (TensorProduct.map A B) =
      (LinearMap.trace Complex K B) • A := by sorry
