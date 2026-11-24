-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_gs_eq_ofReal
-- name    : ReciprocityTheory.Cheb.gs_eq_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:07.694776+00:00
-- url     : https://prove2.me/theorems/63346afe-3e34-4ad2-99f7-12d364c2a967
-- title:
--   Cheb: gs eq of Real
-- statement:
--   The Cheb construction uses the gs eq of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/NormGsEmbZLe.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/NormGsEmbZLe.lean#L12-L17

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

theorem ReciprocityTheory.Cheb.gs_eq_ofReal {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) :
    Gs χ s x = χ (rsgn x : ZMod l) * ((uphi x * (mixedEmbedding.norm x) ^ (-s) : ℝ) : ℂ) := by sorry
