-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverLocal_rawCap_le_iff
-- name    : ThreeSum.TernaryCoverLocal.rawCap_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:47:22.167242+00:00
-- url     : https://prove2.me/theorems/69d9e933-f10c-4f3b-ade7-bb2c58a984a5
-- title:
--   Ternary Cover Local: raw Cap le iff
-- statement:
--   The Ternary Cover Local construction uses the raw Cap le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L195-L206
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L195-L206

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
variable [Fact (Nat.Prime p)]

theorem ThreeSum.TernaryCoverLocal.rawCap_le_iff (α π : DigitType) (w : Coordinate (Fin L) → ZMod p) (τ : ℕ) :
    rawCap α π w ≤ τ ↔ ∀ a b : ZMod p,
      TernaryCoverFibers.rawPairCount (leftHash (α := α) (π := π) w) (rightHash w) a b ≤ τ := by sorry
