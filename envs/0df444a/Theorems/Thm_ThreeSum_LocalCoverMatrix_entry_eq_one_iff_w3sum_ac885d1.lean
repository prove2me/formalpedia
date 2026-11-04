-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverMatrix_entry_eq_one_iff_w3sum_ac885d1
-- name    : ThreeSum.LocalCoverMatrix.entry_eq_one_iff_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:24:56.458902+00:00
-- url     : https://prove2.me/theorems/04737828-5e0d-457e-9522-e32504854cba
-- title:
--   Local Cover Matrix: entry eq one iff
-- statement:
--   The Local Cover Matrix construction uses the entry eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverMatrix.lean#L80-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverMatrix.lean#L80-L134

import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverMatrix
open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes
variable {h L k : ℕ}

theorem ThreeSum.LocalCoverMatrix.entry_eq_one_iff_w3sum_ac885d1 (w : Weight L (LocalField h)) {B a b : ℕ}
    (ha : a < localPrime h) (hb : b < localPrime h) :
    entry w k B (a*localPrime h+b)=1 ↔
      Covers L k B w ((a : LocalField h),(b : LocalField h)) := by sorry
