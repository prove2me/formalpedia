-- Prove2me | Theorems.Thm_QEC_Semantics_ComputationalEmbedding_compress_inner
-- name    : QEC.Semantics.ComputationalEmbedding.compress_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:31:25.530646+00:00
-- url     : https://prove2.me/theorems/173d5543-4572-4a12-804c-9e2c2ed7e961
-- title:
--   Computational Embedding: compress inner
-- statement:
--   The Computational Embedding construction uses the compress inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalEmbedding.lean#L71-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalEmbedding.lean#L71-L75

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.ComputationalEmbedding
open scoped BigOperators
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [Fintype A] [Fintype B] [Fintype C]

theorem QEC.Semantics.ComputationalEmbedding.compress_inner (e : A ↪ B) (E : Operator (EuclideanSpace Complex B))
    (x y : EuclideanSpace Complex A) :
    inner Complex x (compress e E y) = inner Complex (linearMap e x) (E (linearMap e y)) := by sorry
