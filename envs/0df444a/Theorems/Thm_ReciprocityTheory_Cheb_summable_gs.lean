-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_summable_gs
-- name    : ReciprocityTheory.Cheb.summable_gs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:49:18.793839+00:00
-- url     : https://prove2.me/theorems/562c3f34-d345-4f80-8585-3a45c97fce67
-- title:
--   Cheb: summable gs
-- statement:
--   The Cheb construction uses the summable gs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/NormGsEmbZLe.lean#L50-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/NormGsEmbZLe.lean#L50-L80

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_NormGsEmbZLe
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

theorem ReciprocityTheory.Cheb.summable_gs {l : ℕ} (χ : DirichletCharacter ℂ l) (Λ : Submodule ℤ (mixedSpace E)) [DiscreteTopology Λ]
    (hΛ : Module.finrank ℤ Λ = Module.finrank ℚ E) {s : ℝ} (hs : 1 < s) :
    Summable fun x : Λ => Gs χ s (x : mixedSpace E) := by sorry
