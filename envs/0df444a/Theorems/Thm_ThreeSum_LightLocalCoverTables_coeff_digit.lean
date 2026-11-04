-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverTables_coeff_digit
-- name    : ThreeSum.LightLocalCoverTables.coeff_digit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:25:26.410673+00:00
-- url     : https://prove2.me/theorems/27d48541-2ea1-4e1c-bc78-12f582d28f3b
-- title:
--   Light Local Cover Tables: coeff digit
-- statement:
--   The Light Local Cover Tables construction uses the coeff digit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean#L29-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean#L29-L33

import Definitions.Def_Submission_ThreeSum_LightLocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverTables
open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule

theorem ThreeSum.LightLocalCoverTables.coeff_digit (h j : ℕ) (b : Bool) (i : Fin (512*h)) :
    LocalMaskHashes.coeff b (candidate h j) i.val =
      WeightEnumeration.digit (localPrime h) (2*(512*h)) j (2*i.val+(if b then 1 else 0)) := by sorry
