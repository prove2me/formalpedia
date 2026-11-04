-- Prove2me | Theorems.Thm_ThreeSum_LightFiniteTable_stores_ends
-- name    : ThreeSum.LightFiniteTable.stores_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:31:00.563945+00:00
-- url     : https://prove2.me/theorems/1c445e99-6b0b-4d97-87a2-85f449a3004a
-- title:
--   Light Finite Table: stores ends
-- statement:
--   The Light Finite Table construction uses the stores ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFiniteTable.lean#L20-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFiniteTable.lean#L20-L59

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightFiniteTable
set_option autoImplicit false
open ThreeSum ThreeSum.LightFiniteTable
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightFiniteTable.stores_ends (xs : List ℕ) (base offset : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : base+offset+xs.length ≤ lim.space)
    (hvalues : ∀ x ∈ xs, (x : ℤ) ≤ lim.word) :
    Ends lim P d (stores offset xs) ⟨frame [base],μ⟩ (5*xs.length)
      (fun σ => σ.loc=frame [base] ∧
        Seg σ.mem (base+offset) (xs.map (fun (x : ℕ) => (x : ℤ))) ∧
        SameOutside μ σ.mem (base+offset) xs.length) := by sorry
