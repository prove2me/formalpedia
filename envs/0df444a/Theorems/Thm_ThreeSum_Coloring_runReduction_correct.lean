-- Prove2me | Theorems.Thm_ThreeSum_Coloring_runReduction_correct
-- name    : ThreeSum.Coloring.runReduction_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:31.294655+00:00
-- url     : https://prove2.me/theorems/d26e6a82-c5ca-4a8c-bef5-0df740ad1fbc
-- title:
--   Coloring: run Reduction correct
-- statement:
--   Correctness composes with a supplied exact three-set solver. The solver's
--   running time is deliberately not claimed by this reduction theorem.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L205-L216
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L205-L216

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Coloring
set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}

theorem ThreeSum.Coloring.runReduction_correct {n : ℕ} (x : Fin n → ℤ)
    (solve : Finset ℤ → Finset ℤ → Finset ℤ → Bool)
    (hsolve : ∀ a b c, solve a b c = true ↔ ThreeSetWitness a b c) :
    runReduction x solve = true ↔ DistinctZeroSum x := by sorry
