-- Prove2me | Theorems.Thm_ThreeSum_LightLeafSum_partialSum_succ
-- name    : ThreeSum.LightLeafSum.partialSum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:17.002746+00:00
-- url     : https://prove2.me/theorems/a364788d-52b3-49fd-941f-31f8be226b84
-- title:
--   Light Leaf Sum: partial Sum succ
-- statement:
--   The Light Leaf Sum construction uses the partial Sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLeafSum.lean#L24-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLeafSum.lean#L24-L29

import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Definitions.Def_Submission_ThreeSum_LightLeafSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightLeafSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightLeafSum.partialSum_succ {W : ℕ} (Q preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin W))) {j : ℕ} (hj : j < missing.length) :
    partialSum Q preL preR f g stage missing (j+1) =
      partialSum Q preL preR f g stage missing j+term Q preL preR f g stage missing[j] := by sorry
