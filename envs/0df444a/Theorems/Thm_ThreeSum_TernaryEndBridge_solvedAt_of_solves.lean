-- Prove2me | Theorems.Thm_ThreeSum_TernaryEndBridge_solvedAt_of_solves
-- name    : ThreeSum.TernaryEndBridge.solvedAt_of_solves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:41:10.056951+00:00
-- url     : https://prove2.me/theorems/95584219-1e68-4f44-99a2-719698d68830
-- title:
--   Ternary End Bridge: solved At of solves
-- statement:
--   The Ternary End Bridge construction uses the solved At of solves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEndBridge.lean#L27-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEndBridge.lean#L27-L35

import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_Sec3_Theorem22_ThreeSumLayout
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEndBridge
open Light
noncomputable section

theorem ThreeSum.TernaryEndBridge.solvedAt_of_solves {κ : ℕ} {P : Program} {p : ℕ}
    {T : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need} {a : ℝ}
    (hs : Solves s3Task P p T need) (hp : PolyNeed need)
    (ht : ∀ᶠ n : ℕ in Filter.atTop,
      timeUpTo T n ((n : ℝ) ^ (κ : ℝ)) ≤ (n : ℝ) ^ a) :
    ThreeSumApsp.WordRam.SolvedInTimeAt EndStatement.ThreeSum κ a 0 := by sorry
