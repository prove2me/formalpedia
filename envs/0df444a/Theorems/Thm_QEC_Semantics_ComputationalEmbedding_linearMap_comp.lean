-- Prove2me | Theorems.Thm_QEC_Semantics_ComputationalEmbedding_linearMap_comp
-- name    : QEC.Semantics.ComputationalEmbedding.linearMap_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:44:32.735605+00:00
-- url     : https://prove2.me/theorems/905b2bac-5064-4572-89db-e0bb72beedeb
-- title:
--   Computational Embedding: linear Map comp
-- statement:
--   The Computational Embedding construction uses the linear Map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalEmbedding.lean#L58-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalEmbedding.lean#L58-L64

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.ComputationalEmbedding
open scoped BigOperators
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [Fintype A] [Fintype B] [Fintype C]

theorem QEC.Semantics.ComputationalEmbedding.linearMap_comp (e : A ↪ B) (f : B ↪ C) :
    linearMap (e.trans f) = (linearMap f).comp (linearMap e) := by sorry
