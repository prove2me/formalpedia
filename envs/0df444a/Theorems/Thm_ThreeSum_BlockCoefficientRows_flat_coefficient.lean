-- Prove2me | Theorems.Thm_ThreeSum_BlockCoefficientRows_flat_coefficient
-- name    : ThreeSum.BlockCoefficientRows.flat_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:55:20.671246+00:00
-- url     : https://prove2.me/theorems/8d743a8a-9be6-4915-9e50-d50fc858bd20
-- title:
--   Block Coefficient Rows: flat coefficient
-- statement:
--   The Block Coefficient Rows construction uses the flat coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockCoefficientRows.lean#L77-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockCoefficientRows.lean#L77-L83

import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
set_option autoImplicit false
open ThreeSum ThreeSum.BlockCoefficientRows
open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds

theorem ThreeSum.BlockCoefficientRows.flat_coefficient {h J : ℕ} (o : Occurrences h J) (b : Bool) :
    flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h b) =
      OneHotMask.extend (coefficient o b ∘ (coordEquiv J (512*h)).symm) := by sorry
