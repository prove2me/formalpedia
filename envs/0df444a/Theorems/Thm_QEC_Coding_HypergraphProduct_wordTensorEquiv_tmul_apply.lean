-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_wordTensorEquiv_tmul_apply
-- name    : QEC.Coding.HypergraphProduct.wordTensorEquiv_tmul_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:31:19.909207+00:00
-- url     : https://prove2.me/theorems/c28b50f5-4238-4bc3-9774-1978f6ebba79
-- title:
--   Hypergraph Product: word Tensor Equiv tmul apply
-- statement:
--   The Hypergraph Product construction uses the word Tensor Equiv tmul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Realization.lean#L31-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Realization.lean#L31-L37

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Coordinates
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Realization
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v w
open TensorProduct

theorem QEC.Coding.HypergraphProduct.wordTensorEquiv_tmul_apply
    {F : Type u} {A : Type v} {B : Type w}
    [Field F] [Fintype B] [DecidableEq B]
    (x : Word F A) (y : Word F B) (a : A) (b : B) :
    wordTensorEquiv F A B (x ⊗ₜ[F] y) (a, b) = x a * y b := by sorry
