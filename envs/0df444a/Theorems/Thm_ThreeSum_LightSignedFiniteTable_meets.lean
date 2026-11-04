-- Prove2me | Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
-- name    : ThreeSum.LightSignedFiniteTable.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:40:37.828597+00:00
-- url     : https://prove2.me/theorems/0a051699-4a7d-4d9d-903d-5802e931e4e1
-- title:
--   Light Signed Finite Table: meets
-- statement:
--   The Light Signed Finite Table construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedFiniteTable.lean#L55-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedFiniteTable.lean#L55-L73

import Definitions.Def_Submission_ThreeSum_LightFiniteTable
import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Theorems.Thm_ThreeSum_LightFiniteTable_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedFiniteTable
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSignedFiniteTable.meets {p : ℕ} {xs : List ℤ} (hprog : P[p]? = some (body xs))
    (base : ℕ) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : base+xs.length ≤ lim.space) (hvalues : ∀ x ∈ xs, |x| ≤ lim.word) :
    Meets lim P p d [base] μ (7*xs.length+2)
      (fun r ν => r=(xs.length : ℤ) ∧ Seg ν base xs ∧ SameOutside μ ν base xs.length) := by sorry
