-- Prove2me | Theorems.Thm_ThreeSum_Bands_exact_equation_relevant
-- name    : ThreeSum.Bands.exact_equation_relevant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:56.695912+00:00
-- url     : https://prove2.me/theorems/8d234f4b-d4d3-4a83-8d78-44501b2d1f5b
-- title:
--   Bands: exact equation relevant
-- statement:
--   Every exact equation in the input interval hulls survives band filtering.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Bands.lean#L163-L169
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Bands.lean#L163-L169

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Bands
set_option autoImplicit false
open ThreeSum ThreeSum.Bands
variable {I J K : Type*}

theorem ThreeSum.Bands.exact_equation_relevant
    {alo ahi : I → ℤ} {blo bhi : J → ℤ} {clo chi : K → ℤ}
    {i : I} {j : J} {k : K} {a b c : ℤ}
    (ha : alo i ≤ a ∧ a ≤ ahi i) (hb : blo j ≤ b ∧ b ≤ bhi j)
    (hc : clo k ≤ c ∧ c ≤ chi k) (heq : a + b = c) :
    Relevant alo ahi blo bhi clo chi (i, j, k) := by sorry
