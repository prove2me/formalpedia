-- Prove2me | Theorems.Thm_ThreeSum_LightBoxSum_sum_eq_canonical
-- name    : ThreeSum.LightBoxSum.sum_eq_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:17:05.79159+00:00
-- url     : https://prove2.me/theorems/74694e48-8f50-4d92-9ce3-ef8e10b08e04
-- title:
--   Light Box Sum: sum eq canonical
-- statement:
--   The Light Box Sum construction uses the sum eq canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxSum.lean#L179-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxSum.lean#L179-L188

import Definitions.Def_Submission_ThreeSum_LightQueryBox
import Definitions.Def_Submission_ThreeSum_BoxBounds
import Definitions.Def_Submission_ThreeSum_LightBoxSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBoxSum.sum_eq_canonical {L t : ℕ} (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (missing : List (Finset (Fin L))) (hn : missing.Nodup)
    (hmem : ∀ U, U ∈ missing ↔ U ∈ Q.powersetCard t) :
    (missing.map (boxValue Q weight)).sum =
      ∑ U ∈ Q.powersetCard t, SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight := by sorry
