-- Prove2me | Theorems.Thm_ThreeSum_LightPrimality_flag_eq_one_iff
-- name    : ThreeSum.LightPrimality.flag_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:37.218776+00:00
-- url     : https://prove2.me/theorems/c54207eb-80c3-4456-acc8-d53470fc7f8f
-- title:
--   Light Primality: flag eq one iff
-- statement:
--   The Light Primality construction uses the flag eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimality.lean#L35-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimality.lean#L35-L51

import Definitions.Def_Submission_ThreeSum_LightResidues
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_Submission_ThreeSum_LightPrimality
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimality
open Light LightResidues
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.LightPrimality.flag_eq_one_iff (n i : ℕ) : flag n i = 1 ↔ ∀ j < i, ¬ j+2 ∣ n := by sorry
