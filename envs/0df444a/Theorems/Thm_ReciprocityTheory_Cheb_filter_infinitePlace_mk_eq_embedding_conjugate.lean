-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_filter_infinitePlace_mk_eq_embedding_conjugate
-- name    : ReciprocityTheory.Cheb.filter_infinitePlace_mk_eq_embedding_conjugate
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:10.772497+00:00
-- url     : https://prove2.me/theorems/31c19d0a-70f7-556e-bf51-138e4cf5fcc0
-- title:
--   Cheb: filter infinite Place mk eq embedding conjugate
-- statement:
--   The Cheb construction uses the filter infinite Place mk eq embedding conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L60-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L60-L72

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
open NumberField.InfinitePlace

theorem ReciprocityTheory.Cheb.filter_infinitePlace_mk_eq_embedding_conjugate (w : InfinitePlace E) :
    (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by sorry
