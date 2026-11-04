-- Prove2me | Theorems.Thm_ThreeSum_BlockCoefficientRows_occurrenceIndices_fin
-- name    : ThreeSum.BlockCoefficientRows.occurrenceIndices_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:34:30.055168+00:00
-- url     : https://prove2.me/theorems/8248cd8e-3dba-49d5-9a21-e2e780aefb8e
-- title:
--   Block Coefficient Rows: occurrence Indices fin
-- statement:
--   The Block Coefficient Rows construction uses the occurrence Indices fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockCoefficientRows.lean#L55-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockCoefficientRows.lean#L55-L57

import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
set_option autoImplicit false
open ThreeSum ThreeSum.BlockCoefficientRows
open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds

theorem ThreeSum.BlockCoefficientRows.occurrenceIndices_fin {h J : ℕ} (o : Occurrences h J) (i : Fin J) :
    occurrenceIndices o i.val = (o i).val := by sorry
