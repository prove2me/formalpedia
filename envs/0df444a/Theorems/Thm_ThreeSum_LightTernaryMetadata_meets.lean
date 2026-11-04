-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
-- name    : ThreeSum.LightTernaryMetadata.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:41:43.933863+00:00
-- url     : https://prove2.me/theorems/44d4e173-3d89-49b0-8846-f35c8a8ac19d
-- title:
--   Light Ternary Metadata: meets
-- statement:
--   The Light Ternary Metadata construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMetadata.lean#L79-L169
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMetadata.lean#L79-L169

import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryMetadata.meets {pMain pZero pDigit pErase W low high a n powers base d : ℕ}
    (hmain : P[pMain]? = some (body pZero pDigit pErase))
    (hzero : P[pZero]? = some (LightTernaryCodes.zeroBody pErase))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (codes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ base) (hb : base+4*n ≤ powers)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (a+j) = (codes j : ℤ))
    (hpowers : Powers μ powers W)
    (hcodes : ∀ j < n, codes j < 2^W)
    (hlow : low ≤ W) (hhigh : high ≤ W) (hd : d+W+2 ≤ lim.depth) :
    Meets lim P pMain d [W,low,high,a,n,powers,base] μ (time W n)
      (fun _ μ' => (∀ j < n, RecordAt μ' base n j W low high (codes j)) ∧
        SameOutside μ μ' base (4*n)) := by sorry
