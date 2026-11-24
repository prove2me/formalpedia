-- Prove2me | Theorems.Thm_SensitivityUnaryGainNumeric_mem_warmStates
-- name    : SensitivityUnaryGainNumeric.mem_warmStates
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T16:02:37.921315+00:00
-- url     : https://prove2.me/theorems/a8acad6b-d422-4d8e-904c-f5182a082675
-- title:
--   Exact enumeration of warm unary states
-- statement:
--   A state $s=(h,\mathbf g)$ belongs to the warm-state list at rank $j$ exactly when
--   $$
--   0\le h\le12,\qquad |\mathbf g|\le2,\qquad
--   \mathrm{soft}(j)<g\le12\quad\text{for every }g\in\mathbf g.
--   $$
--   The list records occupied guard heights with multiplicity.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryGainNumeric.lean lines 114–134; SHA256 5c1ca2c0fb6d5a3bb3dd3161215b590b131a506c60b0fcab09ef484cb3d7582b; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Range

namespace SensitivityUnaryGainNumeric
end SensitivityUnaryGainNumeric


/-!
Finite prescribed-gain checks for the literal unary recipe.  The weak source
may be ordinary, so soft and hard counts are kept separately.  At a warm
destination only zero, one, or two originally positive soft guards can occur.
All own heights, including the completely false height zero, are covered.
-/
open SensitivityUnaryGainNumeric

theorem SensitivityUnaryGainNumeric.mem_warmStates (r : Recipe) (j : Fin 12) (s : State) :
    s ∈ warmStates r j ↔ s.height ≤ 12 ∧ s.guards.length ≤ 2 ∧
      ∀ old ∈ s.guards, r.soft j < old ∧ old ≤ 12 := by sorry
