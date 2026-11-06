-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finrank_range_le_one_of_all_scalar_compression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finrank_range_le_one_of_all_scalar_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:42.820005+00:00
-- url     : https://prove2.me/theorems/de130465-2fba-436a-92f0-7fc82c1c2519
-- title:
--   BPTCommuting Projector Model: finrank range le one of all scalar compression
-- statement:
--   A symmetric projection whose compression of every ambient operator is scalar
--   has range of dimension at most one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/RankOne.lean#L24-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/RankOne.lean#L24-L48

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RankOne
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped ComplexOrder
universe u
open QEC.Bounds.BPTCommutingProjectorModel

theorem QEC.Bounds.BPTCommutingProjectorModel.finrank_range_le_one_of_all_scalar_compression
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    (P : Semantics.Operator H) (hP : P.IsSymmetricProjection)
    (hscalar : ∀ X : Semantics.Operator H, ∃ scalar : Complex,
      P * X * P = scalar • P) :
    Module.finrank Complex (LinearMap.range P) ≤ 1 := by sorry
