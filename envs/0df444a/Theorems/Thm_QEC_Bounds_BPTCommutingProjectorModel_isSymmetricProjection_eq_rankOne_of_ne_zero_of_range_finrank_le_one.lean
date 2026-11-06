-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_eq_rankOne_of_ne_zero_of_range_finrank_le_one
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_eq_rankOne_of_ne_zero_of_range_finrank_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:34:08.426378+00:00
-- url     : https://prove2.me/theorems/fb98f58d-ee4c-4332-abcb-0d1c34f224bf
-- title:
--   BPTCommuting Projector Model: is Symmetric Projection eq rank One of ne zero of range finrank le one
-- statement:
--   A nonzero finite orthogonal projection with at most one-dimensional range is
--   the rank-one projector onto a normalized vector.  This is the final
--   projection-level conversion used first for the source `Pi_AB'` factor and
--   again for the residual `Theta_{B''C'}` no-cloning factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/RankOne.lean#L29-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/RankOne.lean#L29-L143

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Compression
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_RankOne
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_eq_rankOne_of_ne_zero_of_range_finrank_le_one
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    (P : Semantics.Operator H) (hP : P.IsSymmetricProjection) (hP0 : P ≠ 0)
    (hdim : Module.finrank Complex (LinearMap.range P) ≤ 1) :
    ∃ phi : H, ‖phi‖ = 1 ∧
      P = (InnerProductSpace.rankOne Complex phi phi).toLinearMap := by sorry
