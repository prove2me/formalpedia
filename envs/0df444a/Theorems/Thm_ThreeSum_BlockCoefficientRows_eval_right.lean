-- Prove2me | Theorems.Thm_ThreeSum_BlockCoefficientRows_eval_right
-- name    : ThreeSum.BlockCoefficientRows.eval_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:48:53.999347+00:00
-- url     : https://prove2.me/theorems/f729b4b7-883b-4f5b-8dc8-4c06a09abdfd
-- title:
--   Block Coefficient Rows: eval right
-- statement:
--   The Block Coefficient Rows construction uses the eval right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockCoefficientRows.lean#L94-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockCoefficientRows.lean#L94-L101

import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
set_option autoImplicit false
open ThreeSum ThreeSum.BlockCoefficientRows
open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds

theorem ThreeSum.BlockCoefficientRows.eval_right {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) :
    (OneHotMask.eval
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h true))
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h false))
      (J*(512*h)) (SubsetAddress.subsetMask (indexSet S)) : ℤ) = endpointRight o S := by sorry
