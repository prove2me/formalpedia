-- Prove2me | Theorems.Thm_ThreeSum_LightArgumentTable_stores_ends
-- name    : ThreeSum.LightArgumentTable.stores_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:43.129034+00:00
-- url     : https://prove2.me/theorems/b63f2428-8475-4c01-8c86-cdd0151335c1
-- title:
--   Light Argument Table: stores ends
-- statement:
--   The Light Argument Table construction uses the stores ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightArgumentTable.lean#L13-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightArgumentTable.lean#L13-L45

import Definitions.Def_Submission_ThreeSum_LightFiniteTable
import Definitions.Def_Submission_ThreeSum_LightArgumentTable
import Theorems.Thm_ThreeSum_LightFiniteTable_stores_ends

set_option autoImplicit false
open ThreeSum ThreeSum.LightArgumentTable
open Light
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightArgumentTable.stores_ends (xs : List ℤ) (base offset : ℕ) (loc μ : ℕ → ℤ)
    (hbase : loc 0=(base : ℤ))
    (hread : ∀ (i : ℕ) (hi : i<xs.length), loc (offset+i+1)=xs.getD i 0)
    (hw : (lim.space : ℤ)≤lim.word) (hspace : base+offset+xs.length≤lim.space) :
    Ends lim P depth (stores offset xs.length) ⟨loc,μ⟩ (5*xs.length)
      (fun σ => σ.loc=loc ∧ Seg σ.mem (base+offset) xs ∧
        SameOutside μ σ.mem (base+offset) xs.length) := by sorry
