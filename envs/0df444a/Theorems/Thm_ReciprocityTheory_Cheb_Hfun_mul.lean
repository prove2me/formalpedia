-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_Hfun_mul
-- name    : ReciprocityTheory.Cheb.Hfun_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:48:04.132474+00:00
-- url     : https://prove2.me/theorems/0a56f53d-78a2-419e-b1dc-4c594e0184a2
-- title:
--   Cheb: Hfun mul
-- statement:
--   The Cheb construction uses the Hfun mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/KHoldA.lean#L56-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/KHoldA.lean#L56-L66

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

theorem ReciprocityTheory.Cheb.Hfun_mul {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ) (a : NZIdeal E) :
    Hfun χ b c s (a.1 * b.1) = gfun χ c s a := by sorry
