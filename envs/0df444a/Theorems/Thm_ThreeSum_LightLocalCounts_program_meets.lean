-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCounts_program_meets
-- name    : ThreeSum.LightLocalCounts.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:47:17.989102+00:00
-- url     : https://prove2.me/theorems/8d87c940-6df2-4234-9fcd-2cba688fe641
-- title:
--   Light Local Counts: program meets
-- statement:
--   The Light Local Counts construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCounts.lean#L186-L192
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCounts.lean#L186-L192

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCounts
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCounts
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open Light LocalCoverBounds LightPascal LightSubsetAddress
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLocalCounts.program_meets {μ : ℕ → ℤ} {h dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+4 ≤ lim.depth)
    (hout : dst+6 ≤ work) (hspace : space work h ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim program 0 d [h,dst,work] μ (time h)
      (fun r μ' => r = (localThreshold h : ℤ) ∧ Seg μ' dst (values h) ∧
        KeptBut μ μ' work dst 6) := by sorry
