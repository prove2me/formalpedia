-- Prove2me | Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
-- name    : ThreeSum.LightLeafSum.partialSum_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:53:43.760581+00:00
-- url     : https://prove2.me/theorems/024dde20-f549-4094-9f16-c0db08eec916
-- title:
--   Light Leaf Sum: partial Sum length
-- statement:
--   The Light Leaf Sum construction uses the partial Sum length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLeafSum.lean#L31-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLeafSum.lean#L31-L38

import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Definitions.Def_Submission_ThreeSum_LightLeafSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightLeafSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightLeafSum.partialSum_length {W : ℕ} (Q preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ) (stage : ℕ) (missing : List (Finset (Fin W))) :
    partialSum Q preL preR f g stage missing missing.length =
      (missing.map (term Q preL preR f g stage)).sum := by sorry
