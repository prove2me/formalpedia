-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_latOf_mono
-- name    : ReciprocityTheory.Cheb.latOf_mono
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:49:18.501317+00:00
-- url     : https://prove2.me/theorems/fec7389e-d5c9-59c4-b8b9-4e1b542137e0
-- title:
--   Cheb: lat Of mono
-- statement:
--   The Cheb construction uses the lat Of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L23-L24

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

theorem ReciprocityTheory.Cheb.latOf_mono {I J : Ideal (𝓞 E)} (h : I ≤ J) : latOf I ≤ latOf J := by sorry
