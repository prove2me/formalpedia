-- Prove2me | Theorems.Thm_SensitivityActiveSocketGeometry_conflict_has_direction
-- name    : SensitivityActiveSocketGeometry.conflict_has_direction
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:33:46.003932+00:00
-- url     : https://prove2.me/theorems/f6bf6bc0-64e0-47b6-bbe2-4ed55ba7a1d7
-- title:
--   Every active-side conflict has a directed guard witness
-- statement:
--   Let rows be indexed by $M\times B$, with a macro arc relation, Boolean arc labels, an internal relation on $B$ that covers every distinct pair, and a selected side $a(v)\in\{0,1\}$ for each row. Two distinct rows conflict when they share a macro, or when a macro arc selects the active side at its destination. If $v,w$ conflict, then either the paired guard from $v$ to $w$ contains $(w,a(w))$, or the paired guard from $w$ to $v$ contains $(v,a(v))$, with the corresponding paired arc present.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/ActiveSocketMacroGeometry.lean lines 187–211; SHA256 745d14738e6e657e3f16e79a0836e3cda18124fa37719ea8d258c13fa013f29e; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActiveSocketMacroGeometry
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentGuardCoverage
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityActiveSocketGeometry
end SensitivityActiveSocketGeometry
namespace SensitivityCyclicTokens
end SensitivityCyclicTokens
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-!
Actual selected positive sockets induce the macro conflict graph used in the
population argument. An independent set contains at most one row per macro.
The complement of each selected socket is a coherent token. Every directed
conflict pays for a different actually active guard, including internal OR
checks. Clean domination gives exactly the literal perfect-marker condition.
-/
open SensitivityActiveSocketGeometry
open scoped Classical Fin.CommRing
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge SensitivityCyclicTokens
set_option autoImplicit false
variable {M B I Color : Type} {L n : ℕ}

theorem SensitivityActiveSocketGeometry.conflict_has_direction {macroArc : M → M → Prop}
    {label : M → M → Bool} {internalArc : B → B → Prop}
    (hinternal : CoversPairs internalArc) (active : M × B → Bool)
    {v w : M × B} (h : Conflict macroArc label active v w) :
    DirectedConflict macroArc label internalArc active v w ∨
      DirectedConflict macroArc label internalArc active w v := by sorry
