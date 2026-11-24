-- Prove2me | Theorems.Thm_SensitivityGuardCardinality_paired_guard_socket_count
-- name    : SensitivityGuardCardinality.paired_guard_socket_count
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:13.749121+00:00
-- url     : https://prove2.me/theorems/ff5cda22-a8a9-4ec7-99cb-b40d22273a42
-- title:
--   Exact number of sockets in paired guard checks
-- statement:
--   For paired guards on a finite row set $M\times B$, let $v=(m,b)$ have macro outdegree $d_M(m)$ and internal outdegree $d_B(b)$, excluding loops. Then
--
--   $$\sum_{C\in\mathcal G(v)}|C|=|B|\,d_M(m)+2d_B(b).$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/GuardSocketCardinality.lean lines 109–152; SHA256 1fef0f88b8db3a06fdf51b1ff5a1f952c97bf2e77c90f6ed591f67213bb6f402; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentRegularDegrees
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGuardCardinality
end SensitivityGuardCardinality
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankMapCheckpoint
end SensitivityRankMapCheckpoint
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! Exact physical socket totals for every row of each checkpoint phase. -/
open SensitivityGuardCardinality
open scoped Classical
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityRankMapCheckpoint
open scoped BigOperators

theorem SensitivityGuardCardinality.paired_guard_socket_count {M B : Type} [Fintype M] [Fintype B]
    (macroArc : M → M → Prop) (label : M → M → Bool) (internalArc : B → B → Prop)
    (v : M × B) :
    ∑ check ∈ pairedTournamentGuards macroArc label internalArc v, check.card =
      Fintype.card B * (outNeighbors macroArc v.1).card +
        2 * (outNeighbors internalArc v.2).card := by sorry
