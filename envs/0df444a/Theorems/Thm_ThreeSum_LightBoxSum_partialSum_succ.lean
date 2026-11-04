-- Prove2me | Theorems.Thm_ThreeSum_LightBoxSum_partialSum_succ
-- name    : ThreeSum.LightBoxSum.partialSum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:53:22.244392+00:00
-- url     : https://prove2.me/theorems/8c9dffd9-ae94-4f4f-b331-3240ce5b89db
-- title:
--   Light Box Sum: partial Sum succ
-- statement:
--   The Light Box Sum construction uses the partial Sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxSum.lean#L27-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxSum.lean#L27-L31

import Definitions.Def_Submission_ThreeSum_LightQueryBox
import Definitions.Def_Submission_ThreeSum_BoxBounds
import Definitions.Def_Submission_ThreeSum_LightBoxSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBoxSum.partialSum_succ {L : ℕ} (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (missing : List (Finset (Fin L))) {j : ℕ} (hj : j < missing.length) :
    partialSum Q weight missing (j+1) = partialSum Q weight missing j+boxValue Q weight missing[j] := by sorry
