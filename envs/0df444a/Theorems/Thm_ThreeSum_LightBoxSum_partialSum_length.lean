-- Prove2me | Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
-- name    : ThreeSum.LightBoxSum.partialSum_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:50:47.389408+00:00
-- url     : https://prove2.me/theorems/7819f1eb-1e48-4b92-9130-2bec3dc05ed1
-- title:
--   Light Box Sum: partial Sum length
-- statement:
--   The Light Box Sum construction uses the partial Sum length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxSum.lean#L33-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxSum.lean#L33-L38

import Definitions.Def_Submission_ThreeSum_LightQueryBox
import Definitions.Def_Submission_ThreeSum_BoxBounds
import Definitions.Def_Submission_ThreeSum_LightBoxSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBoxSum.partialSum_length {L : ℕ} (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (missing : List (Finset (Fin L))) :
    partialSum Q weight missing missing.length = (missing.map (boxValue Q weight)).sum := by sorry
