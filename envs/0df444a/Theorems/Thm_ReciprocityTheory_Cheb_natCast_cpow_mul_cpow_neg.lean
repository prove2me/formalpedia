-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_natCast_cpow_mul_cpow_neg
-- name    : ReciprocityTheory.Cheb.natCast_cpow_mul_cpow_neg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:46.949246+00:00
-- url     : https://prove2.me/theorems/d4ddb1bf-7459-5619-bd7a-d123fe83de9b
-- title:
--   Cheb: nat Cast cpow mul cpow neg
-- statement:
--   The Cheb construction uses the nat Cast cpow mul cpow neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/KHoldA.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/KHoldA.lean#L51-L54

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

theorem ReciprocityTheory.Cheb.natCast_cpow_mul_cpow_neg {n : ℕ} (hn : n ≠ 0) (s : ℂ) : (n : ℂ) ^ s * (n : ℂ) ^ (-s) = 1 := by sorry
