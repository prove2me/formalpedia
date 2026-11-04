-- Prove2me | Theorems.Thm_ThreeSum_TernaryEndBridge_endStatement_of_uniform_solvers
-- name    : ThreeSum.TernaryEndBridge.endStatement_of_uniform_solvers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:41:08.884197+00:00
-- url     : https://prove2.me/theorems/cad2c4fc-5a1a-43f7-9a1f-1be164261c8b
-- title:
--   Ternary End Bridge: end Statement of uniform solvers
-- statement:
--   The Ternary End Bridge construction uses the end Statement of uniform solvers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEndBridge.lean#L70-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEndBridge.lean#L70-L80

import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_Sec3_Theorem22_ThreeSumLayout
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEndBridge
open Light
noncomputable section

theorem ThreeSum.TernaryEndBridge.endStatement_of_uniform_solvers {r : ℚ} (hr : 0 ≤ r)
    (h : ∀ κ : ℕ,
      ∃ (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Need),
        Solves s3Task P p T need ∧ PolyNeed need ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ U : ℕ, U ≤ n ^ κ → (T n U : ℝ) ≤ (n : ℝ) ^ (r : ℝ)) :
    EndStatement.ThreeSum.SolvedInTime r := by sorry
