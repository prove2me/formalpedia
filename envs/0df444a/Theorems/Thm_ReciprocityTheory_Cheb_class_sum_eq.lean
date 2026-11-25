-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_class_sum_eq
-- name    : ReciprocityTheory.Cheb.class_sum_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:48:04.667019+00:00
-- url     : https://prove2.me/theorems/c91f1c39-6479-4053-91bf-31afd53279ce
-- title:
--   Cheb: class sum eq
-- statement:
--   The Cheb construction uses the class sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/KHoldA.lean#L89-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/KHoldA.lean#L89-L98

import Definitions.Def_ReciprocityTheory_Chebotarev_NormGsEmbZLe
import Definitions.Def_ReciprocityTheory_Chebotarev_RpowNegFinrankSubOne
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat
import Definitions.Def_ReciprocityTheory_Chebotarev_MeanZero
import Definitions.Def_ReciprocityTheory_Chebotarev_LatSum
import Definitions.Def_ReciprocityTheory_Chebotarev_KHoldA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units Set
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.class_sum_eq {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ)
    (hg : Summable (gfun χ c s)) :
    ∑' a : NZIdeal E, (if cls a * cls b = 1 then gfun χ c s a else 0) =
      ((torsionOrder E : ℕ) : ℂ)⁻¹ * ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) *
        ∑' α : b.1, cfun χ b.1 c.1 (embZ (α : 𝓞 E)) * Gs χ s (embZ (α : 𝓞 E)) := by sorry
