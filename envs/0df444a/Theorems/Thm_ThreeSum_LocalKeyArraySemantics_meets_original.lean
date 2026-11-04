-- Prove2me | Theorems.Thm_ThreeSum_LocalKeyArraySemantics_meets_original
-- name    : ThreeSum.LocalKeyArraySemantics.meets_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:18:27.627203+00:00
-- url     : https://prove2.me/theorems/e41ee266-f9d7-46b7-8a2b-fd0e1c95856d
-- title:
--   Local Key Array Semantics: meets original
-- statement:
--   The Local Key Array Semantics construction uses the meets original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalKeyArraySemantics.lean#L68-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalKeyArraySemantics.lean#L68-L92

import Definitions.Def_Submission_ThreeSum_OutputKeyMasks
import Definitions.Def_Submission_ThreeSum_LightLocalKeys
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
set_option autoImplicit false
open ThreeSum ThreeSum.LocalKeyArraySemantics
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open Light
set_option maxHeartbeats 1800000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LocalKeyArraySemantics.meets_original {pMain h masks maps dst free : ℕ} {μ : ℕ → ℤ}
    (S : LightLocalKeys.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+3 ≤ lim.depth)
    (hspace : LightLocalKeyRow.space free (512*h) (outputCount (512*h) h) ≤ lim.space)
    (hmasks : masks+outputCount (512*h) h ≤ dst)
    (hmaps : maps+scheduleSize h*(2*(512*h)) ≤ dst)
    (hdst : dst+scheduleSize h*outputCount (512*h) h ≤ free)
    (hword : (LightLocalKeys.word (512*h) (localPrime h) (scheduleSize h) : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < outputCount (512*h) h,
      μ (masks+i)=(LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ))
    (hreadFalse : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+i)=(BlockCoefficientRows.mapRow h false j i : ℤ))
    (hreadTrue : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+512*h+i)=(BlockCoefficientRows.mapRow h true j i : ℤ)) :
    Meets lim P pMain d [512*h,masks,outputCount (512*h) h,maps,scheduleSize h,dst,free] μ
      (LightLocalKeys.time (512*h) (outputCount (512*h) h) (scheduleSize h))
      (fun _ ν => Seg ν dst (localKeys h) ∧ Kept μ ν dst) := by sorry
