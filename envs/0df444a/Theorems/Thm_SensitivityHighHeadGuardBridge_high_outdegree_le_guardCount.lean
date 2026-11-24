-- Prove2me | Theorems.Thm_SensitivityHighHeadGuardBridge_high_outdegree_le_guardCount
-- name    : SensitivityHighHeadGuardBridge.high_outdegree_le_guardCount
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:48:58.435873+00:00
-- url     : https://prove2.me/theorems/60667bd2-3362-418c-bca7-e51741cd23c6
-- title:
--   Every outgoing high head occupies a distinct guard
-- statement:
--   Let guards be indexed by the arcs of a directed graph: each arc $v\to w$ has a nonempty check supported on row $w$, and distinct destinations give distinct checks. If every socket of each head $w\in H$ passes cutoff $a$, then
--   $$
--   |\{w\in H:v\to w\}|\le C_a(v,x).
--   $$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/HighHeadGuardBridge.lean lines 98–120; SHA256 a65d8b6636d5eefcc9838f6d69e96a55e7d1b20201ddaaac2d4b039d43d8cb22; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
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

namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-!
The semantic bridge from actual high target sockets to tournament outdegree
budgets. It applies directly to the unary and clustered paired guard families.
Every destination has its own nonempty check, supported only on that row.
-/
open SensitivityHighHeadGuardBridge
open scoped Classical
open SensitivityRankedConstruction SensitivityGuardEvents
set_option autoImplicit false

theorem SensitivityHighHeadGuardBridge.high_outdegree_le_guardCount {V S I Color : Type} {L : ℕ}
    (row : RowFamily I Color L) {guards : GuardFamily V S}
    {arc : V → V → Prop} (idx : GuardIndexing guards arc)
    (H : Finset V) (cutoff : ℕ) (x : ((V × S) × I) → Bool)
    (hhigh : ∀ w ∈ H, ∀ s, passes row cutoff (socketInput x (w,s))) (v : V) :
    (H.filter (arc v)).card ≤ guardCount row guards v cutoff x := by sorry
