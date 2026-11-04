-- Prove2me | Theorems.Thm_ThreeSum_LightFiniteTable_meets
-- name    : ThreeSum.LightFiniteTable.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:29:31.525273+00:00
-- url     : https://prove2.me/theorems/1e4d6c62-22fe-44b4-86f9-3a82e731bb8d
-- title:
--   Light Finite Table: meets
-- statement:
--   The Light Finite Table construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFiniteTable.lean#L63-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFiniteTable.lean#L63-L84

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightFiniteTable
set_option autoImplicit false
open ThreeSum ThreeSum.LightFiniteTable
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightFiniteTable.meets {p : ℕ} {xs : List ℕ} (hprog : P[p]? = some (body xs))
    (base : ℕ) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : base+xs.length ≤ lim.space)
    (hvalues : ∀ x ∈ xs, (x : ℤ) ≤ lim.word) :
    Meets lim P p d [base] μ (5*xs.length+2)
      (fun r ν => r=(xs.length : ℤ) ∧
        Seg ν base (xs.map (fun (x : ℕ) => (x : ℤ))) ∧
        SameOutside μ ν base xs.length) := by sorry
