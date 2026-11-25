-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_tsum_latOf
-- name    : ReciprocityTheory.Cheb.tsum_latOf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:50:46.143296+00:00
-- url     : https://prove2.me/theorems/3b88c573-fbd7-59ca-b45d-5ea2c2d11814
-- title:
--   Cheb: tsum lat Of
-- statement:
--   The Cheb construction uses the tsum lat Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/DiscreteTopologyLatOf.lean#L43-L45

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

theorem ReciprocityTheory.Cheb.tsum_latOf (I : Ideal (𝓞 E)) (g : mixedSpace E → ℂ) :
    ∑' x : latOf I, g x = ∑' α : I, g (embZ (α : 𝓞 E)) := by sorry
