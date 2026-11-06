-- Prove2me | Theorems.Thm_QEC_Semantics_ComputationalEmbedding_linearMap_basis
-- name    : QEC.Semantics.ComputationalEmbedding.linearMap_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:13:03.58426+00:00
-- url     : https://prove2.me/theorems/511390a3-e06e-476d-afb3-1adf8a5bc116
-- title:
--   Computational Embedding: linear Map basis
-- statement:
--   The Computational Embedding construction uses the linear Map basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalEmbedding.lean#L34-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalEmbedding.lean#L34-L39

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.ComputationalEmbedding
open scoped BigOperators
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [Fintype A] [Fintype B] [Fintype C]

theorem QEC.Semantics.ComputationalEmbedding.linearMap_basis (e : A ↪ B) (a : A) :
    linearMap e (EuclideanSpace.basisFun A Complex a) = EuclideanSpace.basisFun B Complex (e a) := by sorry
