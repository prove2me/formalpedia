-- Prove2me | Theorems.Thm_ThreeSum_BlockCoefficientRows_eval_left
-- name    : ThreeSum.BlockCoefficientRows.eval_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:48:31.49968+00:00
-- url     : https://prove2.me/theorems/157cf35b-4941-41b7-9508-f37f9387a7fa
-- title:
--   Block Coefficient Rows: eval left
-- statement:
--   The Block Coefficient Rows construction uses the eval left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockCoefficientRows.lean#L85-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockCoefficientRows.lean#L85-L92

import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
set_option autoImplicit false
open ThreeSum ThreeSum.BlockCoefficientRows
open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds

theorem ThreeSum.BlockCoefficientRows.eval_left {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) :
    (OneHotMask.eval
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h false))
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h true))
      (J*(512*h)) (SubsetAddress.subsetMask (indexSet S)) : ℤ) = endpointLeft o S := by sorry
