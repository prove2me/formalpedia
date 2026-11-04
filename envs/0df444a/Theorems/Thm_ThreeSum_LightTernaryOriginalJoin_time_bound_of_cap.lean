-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryOriginalJoin_time_bound_of_cap
-- name    : ThreeSum.LightTernaryOriginalJoin.time_bound_of_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:12:30.315321+00:00
-- url     : https://prove2.me/theorems/acd3c7bb-0718-4266-bf82-896b5a6ec577
-- title:
--   Light Ternary Original Join: time bound of cap
-- statement:
--   The Light Ternary Original Join construction uses the time bound of cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryOriginalJoin.lean#L75-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryOriginalJoin.lean#L75-L98

import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalJoin
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryOriginalJoin
open Light
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
variable {lim : Limits}

theorem ThreeSum.LightTernaryOriginalJoin.time_bound_of_cap {M NL U D cap : ℕ} {input : ℕ → ℤ}
    {p : ℤ} {base : List ℤ} {J : ℕ} {shift : ℤ}
    (hcap : ∀ i < NL,
      LightHistogram.count
        (fun j => WantedResidueKeys.code M 0 ((keys p base J).getD j 0))
        (WantedResidueKeys.code M shift (input i)) (keys p base J).length ≤ cap) :
    LightWantedSetup.time M input (fun j => (keys p base J).getD j 0)
      NL (keys p base J).length U D shift ≤
      2000*(NL+base.length^J+M+NL*cap+1)*
        (Nat.log 2 (U+1)+Nat.log 2 (M+D+1)+1) := by sorry
