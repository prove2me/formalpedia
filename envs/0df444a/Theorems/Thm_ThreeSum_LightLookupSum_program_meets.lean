-- Prove2me | Theorems.Thm_ThreeSum_LightLookupSum_program_meets
-- name    : ThreeSum.LightLookupSum.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:53.951667+00:00
-- url     : https://prove2.me/theorems/1bb84cf7-0205-47e5-a67e-e9d6c18be458
-- title:
--   Light Lookup Sum: program meets
-- statement:
--   The Light Lookup Sum construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLookupSum.lean#L96-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLookupSum.lean#L96-L107

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightLookupSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightLookupSum
open Light Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLookupSum.program_meets
    {μ : ℕ → ℤ} {keys table n p B : ℕ} (key f : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeys : keys+n ≤ lim.space) (htable : table+p ≤ lim.space)
    (hkey : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hrange : ∀ i < n, key i < p)
    (hread : ∀ r < p, μ (table+r) = (f r : ℤ))
    (hvalue : ∀ r < p, f r ≤ B)
    (hword : (n*B : ℕ) ≤ lim.word) :
    Meets lim program 0 d [keys, table, n, p] μ (time n)
      (fun r μ' => r = (prefixSum f key n : ℤ) ∧ μ' = μ) := by sorry
