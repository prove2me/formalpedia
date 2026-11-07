-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_ker_jointTensorWordMap_eq
-- name    : QEC.Coding.HypergraphProduct.ker_jointTensorWordMap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:36:29.953396+00:00
-- url     : https://prove2.me/theorems/2395b902-b742-4d27-8ef8-67faa2475f92
-- title:
--   Hypergraph Product: ker joint Tensor Word Map eq
-- statement:
--   The Hypergraph Product construction uses the ker joint Tensor Word Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean#L46-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean#L46-L54

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.ker_jointTensorWordMap_eq
    {F : Type v} {A A' B B' : Type u}
    [Field F] [Fintype B] [DecidableEq B]
    [Fintype B'] [DecidableEq B']
    (f : Word F A →ₗ[F] Word F A') (g : Word F B →ₗ[F] Word F B') :
    LinearMap.ker (jointTensorWordMap f g) =
      LinearMap.ker (jointTensorMap f g) := by sorry
