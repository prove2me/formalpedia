-- Prove2me | Theorems.Thm_SensitivityZeroPrefixMarkers_simultaneous_markers_bound
-- name    : SensitivityZeroPrefixMarkers.simultaneous_markers_bound
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:34:12.320052+00:00
-- url     : https://prove2.me/theorems/6482dfa9-dad0-44b9-b773-13c4330662f1
-- title:
--   Zero-budget candidates under simultaneous marker domination
-- statement:
--   Consider paired guards on the finite row set $V=M\times B$, a child Boolean family, a cutoff, and a fixed input. Choose an active side for each candidate row. Assume that the internal relation and the full paired relation cover every pair of distinct vertices. A candidate is cleanly dominated by a marker when the marker's macro has an arc to the candidate's macro whose label avoids the candidate's selected active side. Independence refers to the conflict graph determined by these selected sides. Let $C,H$ be disjoint. Every selected candidate side and both sides of every marker pass the cutoff, while every candidate has zero active guards. Suppose any independent subset of $C$ cleanly dominated by every marker has cardinality at most $\beta$. If $R$ is the total number of active marker-to-candidate incidences, then
--
--   $$|C|\le\beta+R.$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/ZeroPrefixMarkerPopulation.lean lines 14–72; SHA256 417e1543fc2abbe07c9c7b2d89f948963dd86b95b697c6506111a33e22abd4f1; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActiveSocketMacroGeometry
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkedSocketPopulation
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentGuardCoverage
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
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
import Mathlib.Tactic.Tauto

namespace SensitivityActiveSocketGeometry
end SensitivityActiveSocketGeometry
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityMarkedSocketPopulation
end SensitivityMarkedSocketPopulation
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityZeroPrefixMarkers
end SensitivityZeroPrefixMarkers


/-! Simultaneous perfect markers bound the actual zero-failure prefix. -/
open SensitivityZeroPrefixMarkers
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityActiveSocketGeometry SensitivityMarkedSocketPopulation
set_option autoImplicit false
variable {M B I Color : Type} {L : ℕ}

theorem SensitivityZeroPrefixMarkers.simultaneous_markers_bound [Fintype M] [Fintype B]
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (hinternal : CoversPairs internalArc) (hcovers : CoversPairs (pairedArc macroArc internalArc))
    (active : M × B → Bool) (candidates markers : Finset (M × B))
    (hdisj : Disjoint candidates markers) (cutoff beta : ℕ)
    (x : (((M × B) × Bool) × I) → Bool)
    (hactive : ∀ v ∈ candidates, passes row cutoff (socketInput x (v, active v)))
    (hhigh : ∀ v ∈ markers, ∀ b, passes row cutoff (socketInput x (v, b)))
    (hzero : ∀ v ∈ candidates,
      guardCount row (pairedTournamentGuards macroArc label internalArc) v cutoff x = 0)
    (hcap : ∀ t ⊆ candidates, Independent macroArc label active t →
      (∀ v ∈ t, ∀ marker ∈ markers,
        CleanlyDominates macroArc label active marker.1 v) → t.card ≤ beta) :
    candidates.card ≤ beta + ∑ marker ∈ markers,
      (failedIntoCandidates row macroArc label internalArc candidates cutoff x marker).card := by sorry
