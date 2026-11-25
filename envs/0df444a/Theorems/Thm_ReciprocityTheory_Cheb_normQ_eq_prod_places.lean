-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_normQ_eq_prod_places
-- name    : ReciprocityTheory.Cheb.normQ_eq_prod_places
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:23.231671+00:00
-- url     : https://prove2.me/theorems/521e0afc-1fd7-517e-84c2-4ef3321ba496
-- title:
--   Cheb: norm Q eq prod places
-- statement:
--   The Cheb construction uses the norm Q eq prod places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L78-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L78-L101

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

theorem ReciprocityTheory.Cheb.normQ_eq_prod_places (x : E) :
    ((Algebra.norm ℚ x : ℚ) : ℝ) = (∏ w : {w : InfinitePlace E // w.IsReal}, embedding_of_isReal w.2 x) *
      ∏ w : {w : InfinitePlace E // w.IsComplex}, (w.1 x) ^ 2 := by sorry
