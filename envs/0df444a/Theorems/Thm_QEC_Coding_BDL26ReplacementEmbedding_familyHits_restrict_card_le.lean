-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_familyHits_restrict_card_le
-- name    : QEC.Coding.BDL26ReplacementEmbedding.familyHits_restrict_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:41:48.029011+00:00
-- url     : https://prove2.me/theorems/0d827c70-ae67-4187-a775-0f2a160357e4
-- title:
--   BDL26 Replacement Embedding: family Hits restrict card le
-- statement:
--   Restricting a labeled family along an injection can only decrease its geometric hit count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3719-L3727
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3719-L3727

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.familyHits_restrict_card_le {A B : Type*} [Fintype A] [Fintype B]
    (embed : A → B) (hinj : Function.Injective embed) (images : B → Set E) (region : Set E) :
    (familyHits (images ∘ embed) region).card ≤ (familyHits images region).card := by sorry
