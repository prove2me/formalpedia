-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_CardEmbeddingsRestrict_card_embeddings_restrict__3e5c16d106ca
-- name    : P2M_UpperTheory_Reformulated_B_CardEmbeddingsRestrict_card_embeddings_restrict__3e5c16d106ca
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:20:52.269623+00:00
-- url     : https://prove2.me/theorems/c6741d8a-62bf-405b-892c-7b8f2c9b4dfb
-- title:
--   P2 M Upper Theory Reformulated B Card Embeddings Restrict card embeddings restrict  3e5c16d106ca: P2 M Upper Theory Reformulated B Card Embeddings Restrict card embeddings restrict  3e5c16d106ca
-- statement:
--   The P2 M Upper Theory Reformulated B Card Embeddings Restrict card embeddings restrict  3e5c16d106ca construction uses the P2 M Upper Theory Reformulated B Card Embeddings Restrict card embeddings restrict  3e5c16d106ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CardEmbeddingsRestrict.lean#L3-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CardEmbeddingsRestrict.lean#L3-L21

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_CardEmbeddingsRestrict_card_embeddings_restrict__3e5c16d106ca.{u_1, u_2} :
    ∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [NumberField K] [inst_2 : Field L] [inst_3 : NumberField L]
    [inst_4 : Algebra K L] (τ : K →+* ℂ),
    (open Classical in Finset.filter (fun σ : L →+* ℂ => σ.comp (Algebra.algebraMap K L) = τ) Finset.univ).card = Module.finrank K L := by sorry

alias «UpperTheory».«Reformulated».«B».«CardEmbeddingsRestrict».«card_embeddings_restrict».«» := P2M_UpperTheory_Reformulated_B_CardEmbeddingsRestrict_card_embeddings_restrict__3e5c16d106ca
