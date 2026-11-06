-- Prove2me | Theorems.Thm_QEC_Semantics_ComputationalEmbedding_isometry_basis
-- name    : QEC.Semantics.ComputationalEmbedding.isometry_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:44:23.399608+00:00
-- url     : https://prove2.me/theorems/0a7aaf25-7be5-45bf-9be5-592980b8c150
-- title:
--   Computational Embedding: isometry basis
-- statement:
--   The Computational Embedding construction uses the isometry basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalEmbedding.lean#L54-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalEmbedding.lean#L54-L56

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.ComputationalEmbedding
open scoped BigOperators
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [Fintype A] [Fintype B] [Fintype C]

theorem QEC.Semantics.ComputationalEmbedding.isometry_basis (e : A ↪ B) (a : A) :
    isometry e (EuclideanSpace.basisFun A Complex a) = EuclideanSpace.basisFun B Complex (e a) := by sorry
