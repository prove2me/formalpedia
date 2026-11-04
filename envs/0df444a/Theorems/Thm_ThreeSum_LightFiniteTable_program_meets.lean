-- Prove2me | Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
-- name    : ThreeSum.LightFiniteTable.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:29:59.674595+00:00
-- url     : https://prove2.me/theorems/c766644f-0ceb-4d8c-bdb0-0a4225e3fa8f
-- title:
--   Light Finite Table: program meets
-- statement:
--   The Light Finite Table construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFiniteTable.lean#L88-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFiniteTable.lean#L88-L96

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightFiniteTable
set_option autoImplicit false
open ThreeSum ThreeSum.LightFiniteTable
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightFiniteTable.program_meets (xs : List ℕ) (base : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : base+xs.length ≤ lim.space)
    (hvalues : ∀ x ∈ xs, (x : ℤ) ≤ lim.word) :
    Meets lim (program xs) 0 d [base] μ (5*xs.length+2)
      (fun r ν => r=(xs.length : ℤ) ∧
        Seg ν base (xs.map (fun (x : ℕ) => (x : ℤ))) ∧
        SameOutside μ ν base xs.length) := by sorry
