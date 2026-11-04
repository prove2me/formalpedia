-- Prove2me | Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets
-- name    : ThreeSum.LightSignedFiniteTable.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:44:22.060605+00:00
-- url     : https://prove2.me/theorems/bca7c32a-52a4-487f-8958-7c16985c4955
-- title:
--   Light Signed Finite Table: program meets
-- statement:
--   The Light Signed Finite Table construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedFiniteTable.lean#L76-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedFiniteTable.lean#L76-L81

import Definitions.Def_Submission_ThreeSum_LightFiniteTable
import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedFiniteTable
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSignedFiniteTable.program_meets (xs : List ℤ) (base : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : base+xs.length ≤ lim.space)
    (hvalues : ∀ x ∈ xs, |x| ≤ lim.word) :
    Meets lim (program xs) 0 d [base] μ (7*xs.length+2)
      (fun r ν => r=(xs.length : ℤ) ∧ Seg ν base xs ∧ SameOutside μ ν base xs.length) := by sorry
