-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_finrank_latOf
-- name    : ReciprocityTheory.Cheb.finrank_latOf
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:47:59.64475+00:00
-- url     : https://prove2.me/theorems/a8a83ec4-4e4a-5901-b2e6-8214dd3a9574
-- title:
--   Cheb: finrank lat Of
-- statement:
--   The Cheb construction uses the finrank lat Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L33-L35

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

theorem ReciprocityTheory.Cheb.finrank_latOf {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) : Module.finrank ℤ (latOf I) = Module.finrank ℚ E := by sorry
