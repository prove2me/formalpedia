-- Prove2me | Theorems.Thm_SensitivityMarkedPseudoforestPopulation_marked_sinks_inequality
-- name    : SensitivityMarkedPseudoforestPopulation.marked_sinks_inequality
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:34:10.69157+00:00
-- url     : https://prove2.me/theorems/b139b799-fc4c-468c-aeba-c88bbeb47d67
-- title:
--   Marked pseudoforest inequality for designated sinks
-- statement:
--   Consider paired guards on the finite row set $V=M\times B$, a child Boolean family, a cutoff, and a fixed input. Choose an active side for each candidate row. Assume that the internal relation and the full paired relation cover every pair of distinct vertices. A candidate is cleanly dominated by a marker when the marker's macro has an arc to the candidate's macro whose label avoids the candidate's selected active side. Independence refers to the conflict graph determined by these selected sides. Let $C,H$ be disjoint, and let $Z\subseteq C$ be sinks of the directed candidate-conflict relation. Each selected candidate side passes the cutoff, and each candidate has at most one active guard. Suppose every independent candidate subset cleanly dominated by a marker has size at most $\beta$. Write $N=|C|$, $m=|H|$, let $T$ count arcs from candidates in $C$ to markers in $H$, and let $R$ count active guard checks from markers to candidates, with incidences counted separately for each source. Then
--
--   $$m(N+|Z|)\le3m\beta+2(T+R).$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MarkedPseudoforestPopulation.lean lines 54–119; SHA256 1da888bf3cbf416836be7139ea98298c6664f21a2324b6b3845ef18ed6a4facc; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActiveSocketMacroGeometry
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkedSocketPopulation
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PseudoforestCover
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
namespace SensitivityActiveSocketPopulation
end SensitivityActiveSocketPopulation
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityMarkedPseudoforestPopulation
end SensitivityMarkedPseudoforestPopulation
namespace SensitivityMarkedSocketPopulation
end SensitivityMarkedSocketPopulation
namespace SensitivityPseudoforest
end SensitivityPseudoforest
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! The marked pseudoforest inequalities, including genuine marker-budget sinks. -/
open SensitivityMarkedPseudoforestPopulation
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityActiveSocketGeometry SensitivityActiveSocketPopulation
open SensitivityMarkedSocketPopulation SensitivityPseudoforest
set_option autoImplicit false
variable {V M B I Color : Type} {L : ℕ}

theorem SensitivityMarkedPseudoforestPopulation.marked_sinks_inequality [Fintype M] [Fintype B]
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (hinternal : CoversPairs internalArc) (hcovers : CoversPairs (pairedArc macroArc internalArc))
    (active : M × B → Bool) (candidates markers sinks : Finset (M × B))
    (hdisj : Disjoint candidates markers) (hsinks : sinks ⊆ candidates) (cutoff beta : ℕ)
    (x : (((M × B) × Bool) × I) → Bool)
    (hactive : ∀ v ∈ candidates, passes row cutoff (socketInput x (v, active v)))
    (hbudget : ∀ v ∈ candidates,
      guardCount row (pairedTournamentGuards macroArc label internalArc) v cutoff x ≤ 1)
    (hsink : ∀ v ∈ sinks,
      IsSink (DirectedConflict macroArc label internalArc active) candidates v)
    (hcap : ∀ marker ∈ markers, ∀ t ⊆ candidates, Independent macroArc label active t →
      (∀ v ∈ t, CleanlyDominates macroArc label active marker.1 v) → t.card ≤ beta) :
    markers.card * (candidates.card + sinks.card) ≤ markers.card * (3 * beta) +
      2 * ((∑ v ∈ candidates, (toMarkers (pairedArc macroArc internalArc) markers v).card) +
        (∑ marker ∈ markers,
          (failedIntoCandidates row macroArc label internalArc candidates cutoff x marker).card)) := by sorry
