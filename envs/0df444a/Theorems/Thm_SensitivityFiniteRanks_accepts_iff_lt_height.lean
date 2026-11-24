-- Prove2me | Theorems.Thm_SensitivityFiniteRanks_accepts_iff_lt_height
-- name    : SensitivityFiniteRanks.accepts_iff_lt_height
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:48:53.506391+00:00
-- url     : https://prove2.me/theorems/f3f7d762-a5d1-4e2b-a780-fcb158966122
-- title:
--   Acceptance is equivalent to lying below the rank height
-- statement:
--   For a nested colored family $F$ with ranks $0,\ldots,L-1$, define its rank height at $x$ as the maximum of $r+1$ over accepted ranks, with value zero when no rank is accepted. Then
--   $$
--   F\text{ accepts rank }j\text{ at }x
--   \quad\Longleftrightarrow\quad j<\operatorname{rankHeight}_F(x).
--   $$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/FiniteRanks.lean lines 32–46; SHA256 5b8683b5ea607ba70428c9c2d448954bbb81198e4f3a3b0466ad29e78fcecf41; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_FiniteRanks
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-!
Finite rank states for actual nested Boolean families. Height zero is the
all-false state; height r+1 is exact rank r. This makes every enumerated state
finite without encoding the all-false case by truncated natural subtraction.
-/
open SensitivityFiniteRanks
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
set_option autoImplicit false
variable {I Color V S : Type} {L : ℕ}

theorem SensitivityFiniteRanks.accepts_iff_lt_height {row : RowFamily I Color L} (hnested : Nested row)
    (j : Fin L) (x : I → Bool) : accepts row j x ↔ j.val < rankHeight row x := by sorry
