-- Prove2me | Theorems.Thm_SensitivityActiveSocketGeometry_directedConflict_outdegree_le_guardCount
-- name    : SensitivityActiveSocketGeometry.directedConflict_outdegree_le_guardCount
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:33:48.462694+00:00
-- url     : https://prove2.me/theorems/a4b78246-2823-41d5-915a-c2fe6c116bf8
-- title:
--   Active-side conflict outdegree is bounded by guard count
-- statement:
--   Consider paired guards on a finite row set $M\times B$, a child family, a cutoff, and an input. Let $S$ be a finite candidate set with a chosen side $a(w)$ passing the cutoff for every $w\in S$. For every source row $v$, let $D_S(v)$ be the candidates $w\in S$ for which the paired arc $v\to w$ exists and its guard contains $(w,a(w))$. If $g(v)$ is the number of active guards at $v$, then
--
--   $$|D_S(v)|\le g(v).$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/ActiveSocketMacroGeometry.lean lines 241–263; SHA256 745d14738e6e657e3f16e79a0836e3cda18124fa37719ea8d258c13fa013f29e; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActiveSocketMacroGeometry
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
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

theorem SensitivityActiveSocketGeometry.directedConflict_outdegree_le_guardCount [Fintype M] [Fintype B]
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (active : M × B → Bool) (vertices : Finset (M × B)) (cutoff : ℕ)
    (x : (((M × B) × Bool) × I) → Bool)
    (hactive : ∀ w ∈ vertices, passes row cutoff (socketInput x (w, active w)))
    (v : M × B) :
    (vertices.filter (DirectedConflict macroArc label internalArc active v)).card ≤
      guardCount row (pairedTournamentGuards macroArc label internalArc) v cutoff x := by sorry
