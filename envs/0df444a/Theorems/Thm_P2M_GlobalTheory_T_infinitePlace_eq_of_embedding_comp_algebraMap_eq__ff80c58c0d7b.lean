-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_infinitePlace_eq_of_embedding_comp_algebraMap_eq__ff80c58c0d7b
-- name    : P2M_GlobalTheory_T_infinitePlace_eq_of_embedding_comp_algebraMap_eq__ff80c58c0d7b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:26.740902+00:00
-- url     : https://prove2.me/theorems/3cb6c13b-c924-4954-aa2b-f6f168ae8dcd
-- title:
--   P2 M Global Theory T infinite Place eq of embedding comp algebra Map eq  ff80c58c0d7b: P2 M Global Theory T infinite Place eq of embedding comp algebra Map eq  ff80c58c0d7b
-- statement:
--   The P2 M Global Theory T infinite Place eq of embedding comp algebra Map eq  ff80c58c0d7b construction uses the P2 M Global Theory T infinite Place eq of embedding comp algebra Map eq  ff80c58c0d7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InfinitePlaceEqOfEmbeddingCompAlgebraMapEqStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InfinitePlaceEqOfEmbeddingCompAlgebraMapEqStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InfinitePlaceEqOfEmbeddingCompAlgebraMapEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InfinitePlaceEqOfEmbeddingCompAlgebraMapEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_infinitePlace_eq_of_embedding_comp_algebraMap_eq__ff80c58c0d7b : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w₁ w₂ : InfinitePlace E), w₁.embedding.comp (algebraMap F E) = w₂.embedding.comp (algebraMap F E) → w₁ = w₂ := by sorry

alias «GlobalTheory».«T».«infinitePlace_eq_of_embedding_comp_algebraMap_eq'» := P2M_GlobalTheory_T_infinitePlace_eq_of_embedding_comp_algebraMap_eq__ff80c58c0d7b
