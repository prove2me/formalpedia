-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_norm_embZ_ne_zero
-- name    : ReciprocityTheory.Cheb.norm_embZ_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:52.963557+00:00
-- url     : https://prove2.me/theorems/8eb7ce49-7634-5b25-8538-424cca230ba6
-- title:
--   Cheb: norm emb Z ne zero
-- statement:
--   The Cheb construction uses the norm emb Z ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/IdealLat.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/IdealLat.lean#L24-L27

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat
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

theorem ReciprocityTheory.Cheb.norm_embZ_ne_zero {g : 𝓞 E} (hg : g ≠ 0) : mixedEmbedding.norm (embZ g) ≠ 0 := by sorry
