-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_allocated_program_meets
-- name    : ThreeSum.LightWeightedGlobalPrefixSetup.allocated_program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:51:14.919878+00:00
-- url     : https://prove2.me/theorems/e0166b09-8444-4385-befb-fd80bf63e24d
-- title:
--   Light Weighted Global Prefix Setup: allocated program meets
-- statement:
--   The Light Weighted Global Prefix Setup construction uses the allocated program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L269-L277
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L269-L277

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_EnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixSetup
open Light LightSubsetAddress WeightedAddresses WeightedBankEnumeration
open WeightedGlobalLocalParameters WeightedGlobalDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedGlobalPrefixSetup.allocated_program_meets {m j F free d : ℕ} (μ : ℕ→ ℤ)
    (hw : (lim.space:ℤ)≤ lim.word) (hspace : endAt free m j≤ lim.space)
    (hword : (word m j F:ℤ)≤ lim.word) (hd : d+N m j+4≤ lim.depth) :
    Meets lim allocatedProgram 5 d [j,m,F,free] μ (allocateTime m j)
      (fun r ν=>r=(headerAt free m j:ℤ) ∧
        Seg ν (headerAt free m j) (header m j F free (workAt free m j)) ∧
        Seg ν free ((codes (N m j) (T m j)).map (fun (c:ℕ)=>(c:ℤ))) ∧
        Powers ν (workAt free m j) (2*N m j) ∧ Kept μ ν free) := by sorry
