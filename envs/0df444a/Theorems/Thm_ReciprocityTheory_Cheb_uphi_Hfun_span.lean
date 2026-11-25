-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_uphi_Hfun_span
-- name    : ReciprocityTheory.Cheb.uphi_Hfun_span
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:50:03.314464+00:00
-- url     : https://prove2.me/theorems/8ffe73f9-3604-4f84-8244-38ec6fc7ca44
-- title:
--   Cheb: uphi Hfun span
-- statement:
--   The Cheb construction uses the uphi Hfun span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/KHoldA.lean#L68-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/KHoldA.lean#L68-L87

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

theorem ReciprocityTheory.Cheb.uphi_Hfun_span {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ) (α : b.1) :
    ((uphi (embZ (α : 𝓞 E)) : ℝ) : ℂ) * Hfun χ b c s (Ideal.span {(α : 𝓞 E)}) =
      ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) *
        (cfun χ b.1 c.1 (embZ (α : 𝓞 E)) * Gs χ s (embZ (α : 𝓞 E))) := by sorry
