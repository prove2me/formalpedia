-- Prove2me | Theorems.Thm_ThreeSum_LightSignedFiniteTable_stores_ends
-- name    : ThreeSum.LightSignedFiniteTable.stores_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:38:34.460991+00:00
-- url     : https://prove2.me/theorems/c1ea1118-d72f-438a-8fdb-5a0b786f78b0
-- title:
--   Light Signed Finite Table: stores ends
-- statement:
--   The Light Signed Finite Table construction uses the stores ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedFiniteTable.lean#L14-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedFiniteTable.lean#L14-L51

import Definitions.Def_Submission_ThreeSum_LightFiniteTable
import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Theorems.Thm_ThreeSum_LightFiniteTable_stores_ends

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedFiniteTable
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSignedFiniteTable.stores_ends (xs : List ℤ) (base offset : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : base+offset+xs.length ≤ lim.space)
    (hvalues : ∀ x ∈ xs, |x| ≤ lim.word) :
    Ends lim P d (stores offset xs) ⟨frame [base],μ⟩ (7*xs.length)
      (fun σ => σ.loc=frame [base] ∧ Seg σ.mem (base+offset) xs ∧
        SameOutside μ σ.mem (base+offset) xs.length) := by sorry
