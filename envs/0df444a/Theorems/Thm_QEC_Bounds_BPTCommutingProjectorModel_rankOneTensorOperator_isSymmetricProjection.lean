-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rankOneTensorOperator_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.rankOneTensorOperator_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-18T04:18:39.156397+00:00
-- url     : https://prove2.me/theorems/325e9469-b038-4abd-9a83-80a612ab5d1d
-- title:
--   BPTCommuting Projector Model: rank One Tensor Operator is Symmetric Projection
-- statement:
--   A normalized rank-one tensor a symmetric projection is a symmetric projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L458-L466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L458-L466

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.rankOneTensorOperator_isSymmetricProjection
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (v : H) (hv : ‖v‖ = 1) (P : Semantics.Operator K)
    (hP : P.IsSymmetricProjection) :
    (rankOneTensorOperator v P).IsSymmetricProjection := by sorry
