-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_unit_smul_embZ
-- name    : ReciprocityTheory.Cheb.unit_smul_embZ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:49:04.762878+00:00
-- url     : https://prove2.me/theorems/d3983328-8cff-462e-a6f4-3c04cb92d3f8
-- title:
--   Cheb: unit smul emb Z
-- statement:
--   The Cheb construction uses the unit smul emb Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L47-L49

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

theorem ReciprocityTheory.Cheb.unit_smul_embZ (u : (𝓞 E)ˣ) (α : 𝓞 E) : u • embZ α = embZ ((u : 𝓞 E) * α) := by sorry
