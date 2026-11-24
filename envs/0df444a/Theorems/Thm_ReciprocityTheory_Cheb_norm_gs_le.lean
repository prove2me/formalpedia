-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_norm_gs_le
-- name    : ReciprocityTheory.Cheb.norm_gs_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:57.847831+00:00
-- url     : https://prove2.me/theorems/41cbc3d5-0d07-4485-a43d-1a5e39814e77
-- title:
--   Cheb: norm gs le
-- statement:
--   The Cheb construction uses the norm gs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/NormGsEmbZLe.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/NormGsEmbZLe.lean#L19-L24

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

theorem ReciprocityTheory.Cheb.norm_gs_le {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) :
    ‖Gs χ s x‖ ≤ uphi x * (mixedEmbedding.norm x) ^ (-s) := by sorry
