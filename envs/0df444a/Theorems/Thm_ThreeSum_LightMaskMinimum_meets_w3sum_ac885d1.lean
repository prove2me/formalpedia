-- Prove2me | Theorems.Thm_ThreeSum_LightMaskMinimum_meets_w3sum_ac885d1
-- name    : ThreeSum.LightMaskMinimum.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:17:06.922266+00:00
-- url     : https://prove2.me/theorems/0e26a1fb-a455-413a-9d42-ab4cd8b56cb2
-- title:
--   Light Mask Minimum: meets
-- statement:
--   The Light Mask Minimum construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskMinimum.lean#L38-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskMinimum.lean#L38-L131

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_LightMaskMinimum
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c

set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskMinimum
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightMaskMinimum.meets_w3sum_ac885d1 {pMain pPowers pErase : ℕ}
    (hmain : P[pMain]? = some (body pPowers pErase))
    (hPowers : P[pPowers]? = some powTableBody)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L work d : ℕ} (S : Finset (Fin L)) (hS : S.Nonempty)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [L,subsetMask S,work] μ (time L)
      (fun r μ' => r = ((S.min' hS).val : ℤ) ∧ Kept μ μ' work) := by sorry
