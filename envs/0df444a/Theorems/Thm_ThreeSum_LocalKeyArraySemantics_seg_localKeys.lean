-- Prove2me | Theorems.Thm_ThreeSum_LocalKeyArraySemantics_seg_localKeys
-- name    : ThreeSum.LocalKeyArraySemantics.seg_localKeys
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:18:00.352471+00:00
-- url     : https://prove2.me/theorems/b821fd67-8107-4369-8ba5-306563620f23
-- title:
--   Local Key Array Semantics: seg local Keys
-- statement:
--   The Local Key Array Semantics construction uses the seg local Keys property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalKeyArraySemantics.lean#L47-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalKeyArraySemantics.lean#L47-L64

import Definitions.Def_Submission_ThreeSum_OutputKeyMasks
import Definitions.Def_Submission_ThreeSum_LightLocalKeys
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
set_option autoImplicit false
open ThreeSum ThreeSum.LocalKeyArraySemantics
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open Light
set_option maxHeartbeats 1800000

theorem ThreeSum.LocalKeyArraySemantics.seg_localKeys {h dst : ℕ} {μ : ℕ → ℤ}
    (hout : ∀ j < scheduleSize h, ∀ i < outputCount (512*h) h,
      μ (dst+j*outputCount (512*h) h+i)=
        (OneHotMask.eval (BlockCoefficientRows.mapRow h true j) (fun _ => 0) (512*h)
          (LocalMaskGraph.maskAt (512*h) (2*h) i) : ℤ)-
        (OneHotMask.eval (BlockCoefficientRows.mapRow h false j) (fun _ => 0) (512*h)
          (LocalMaskGraph.maskAt (512*h) (2*h) i) : ℤ)) :
    Seg μ dst (localKeys h) := by sorry
