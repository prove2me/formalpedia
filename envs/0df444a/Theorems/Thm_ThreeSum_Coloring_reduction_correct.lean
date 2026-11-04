-- Prove2me | Theorems.Thm_ThreeSum_Coloring_reduction_correct
-- name    : ThreeSum.Coloring.reduction_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:02:52.067355+00:00
-- url     : https://prove2.me/theorems/72b173ae-ef3a-4a73-8dda-51ed1792045f
-- title:
--   Coloring: reduction correct
-- statement:
--   Exact equivalence between an array 3SUM witness at distinct positions and
--   one of the enumerated, deduplicated three-set instances.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L170-L193
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L170-L193

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

theorem ThreeSum.Coloring.reduction_correct {n : ℕ} (x : Fin n → ℤ) :
    DistinctZeroSum x ↔ ∃ c ∈ family n,
      ThreeSetWitness (values x c 0) (values x c 1) (negValues x c) := by sorry
