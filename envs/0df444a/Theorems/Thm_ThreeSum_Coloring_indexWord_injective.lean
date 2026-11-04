-- Prove2me | Theorems.Thm_ThreeSum_Coloring_indexWord_injective
-- name    : ThreeSum.Coloring.indexWord_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:09:14.939791+00:00
-- url     : https://prove2.me/theorems/730ae445-3e8e-4fb9-84ce-99d1a9027a98
-- title:
--   Coloring: index Word injective
-- statement:
--   The Coloring construction uses the index Word injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L90-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L90-L99

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

theorem ThreeSum.Coloring.indexWord_injective (n : ℕ) : Function.Injective (@indexWord n) := by sorry
