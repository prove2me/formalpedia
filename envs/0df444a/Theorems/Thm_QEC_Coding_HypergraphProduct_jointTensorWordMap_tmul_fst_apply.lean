-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_jointTensorWordMap_tmul_fst_apply
-- name    : QEC.Coding.HypergraphProduct.jointTensorWordMap_tmul_fst_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:35:19.202116+00:00
-- url     : https://prove2.me/theorems/e76f70f0-3831-425c-8b4b-4306ebb72784
-- title:
--   Hypergraph Product: joint Tensor Word Map tmul fst apply
-- statement:
--   The Hypergraph Product construction uses the joint Tensor Word Map tmul fst apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean#L94-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean#L94-L100

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Realization
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
open TensorProduct

theorem QEC.Coding.HypergraphProduct.jointTensorWordMap_tmul_fst_apply
    {F : Type v} {A A' B B' : Type u}
    [Field F] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (f : Word F A →ₗ[F] Word F A') (g : Word F B →ₗ[F] Word F B')
    (x : Word F A) (y : Word F B) (a' : A') (b : B) :
    (jointTensorWordMap f g (x ⊗ₜ[F] y)).1 (a', b) = f x a' * y b := by sorry
