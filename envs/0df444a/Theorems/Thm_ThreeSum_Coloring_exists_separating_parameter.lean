-- Prove2me | Theorems.Thm_ThreeSum_Coloring_exists_separating_parameter
-- name    : ThreeSum.Coloring.exists_separating_parameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:22:25.70423+00:00
-- url     : https://prove2.me/theorems/c92e5505-47a9-48a0-9759-823837e95ed9
-- title:
--   Coloring: exists separating parameter
-- statement:
--   Enumeration of the small parameter space separates the words in the
--   specified order, so no permutation of the three-set equation is needed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L69-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L69-L79

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

theorem ThreeSum.Coloring.exists_separating_parameter {d : ℕ} {s t u : Fin d → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    ∃ p : Parameter d, applyColor p s = 0 ∧ applyColor p t = 1 ∧
      applyColor p u = 2 := by sorry
