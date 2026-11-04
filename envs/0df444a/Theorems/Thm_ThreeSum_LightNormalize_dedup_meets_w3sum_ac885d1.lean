-- Prove2me | Theorems.Thm_ThreeSum_LightNormalize_dedup_meets_w3sum_ac885d1
-- name    : ThreeSum.LightNormalize.dedup_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:37.605201+00:00
-- url     : https://prove2.me/theorems/e51e0708-89ce-4e58-a6bd-70dba3c5f084
-- title:
--   Light Normalize: dedup meets
-- statement:
--   The Light Normalize construction uses the dedup meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNormalize.lean#L52-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNormalize.lean#L52-L123

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Mathlib.Data.List.Dedup
import Definitions.Def_Submission_ThreeSum_LightNormalize
set_option autoImplicit false
open ThreeSum ThreeSum.LightNormalize
open Light
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightNormalize.dedup_meets_w3sum_ac885d1 {pDedup : ℕ}
    (hprog : P[pDedup]? = some (dedupBody pDedup))
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) :
    ∀ (L : List ℤ) (μ : ℕ → ℤ) (src dst d : ℕ),
      L.Pairwise (· ≤ ·) → Seg μ src L → src+L.length ≤ dst →
      dst+L.length ≤ lim.space → d+L.length ≤ lim.depth →
      Meets lim P pDedup d [src,L.length,dst] μ (dedupTime L.length)
        (fun r μ' => r = (L.dedup.length : ℤ) ∧ Seg μ' dst L.dedup ∧
          SameOutside μ μ' dst L.length) := by sorry
