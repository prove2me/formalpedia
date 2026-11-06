-- Prove2me | Theorems.Thm_QEC_Semantics_ComputationalEmbedding_compress_basis_inner
-- name    : QEC.Semantics.ComputationalEmbedding.compress_basis_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:44:26.165551+00:00
-- url     : https://prove2.me/theorems/e80a73c7-a46b-4ba0-af6f-9bb06241cc36
-- title:
--   Computational Embedding: compress basis inner
-- statement:
--   The Computational Embedding construction uses the compress basis inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalEmbedding.lean#L77-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalEmbedding.lean#L77-L83

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.ComputationalEmbedding
open scoped BigOperators
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [Fintype A] [Fintype B] [Fintype C]

theorem QEC.Semantics.ComputationalEmbedding.compress_basis_inner (e : A ↪ B) (E : Operator (EuclideanSpace Complex B))
    (a b : A) :
    inner Complex (EuclideanSpace.basisFun A Complex a)
        (compress e E (EuclideanSpace.basisFun A Complex b)) =
      inner Complex (EuclideanSpace.basisFun B Complex (e a))
        (E (EuclideanSpace.basisFun B Complex (e b))) := by sorry
