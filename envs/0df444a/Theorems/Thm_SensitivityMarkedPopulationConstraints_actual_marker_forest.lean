-- Prove2me | Theorems.Thm_SensitivityMarkedPopulationConstraints_actual_marker_forest
-- name    : SensitivityMarkedPopulationConstraints.actual_marker_forest
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:33:54.844357+00:00
-- url     : https://prove2.me/theorems/ae771cef-8a49-4e12-85bd-f04b49a26a56
-- title:
--   Explicit marked forest constraint
-- statement:
--   Consider paired guards on the finite row set $V=M\times B$, a child Boolean family, a cutoff, and a fixed input. Choose an active side for each candidate row. Assume that the internal relation and the full paired relation cover every pair of distinct vertices. A candidate is cleanly dominated by a marker when the marker's macro has an arc to the candidate's macro whose label avoids the candidate's selected active side. Independence refers to the conflict graph determined by these selected sides. Let $C,H$ be disjoint with $m=|H|>0$, and let $Z\subseteq C$ consist of zero-guard candidates. Selected candidate sides and both sides of every marker pass the cutoff, and every candidate has at most one active guard. Suppose the unmarked and one-marker independence caps are $\alpha$ and $\beta$, and the total active marker-to-candidate incidence count is at most $\rho$. Put $F=|C|+|Z|$. Then
--
--   $$\begin{cases}
--   2F\le3(\alpha+\beta)+2\rho,&m=1,\\
--   mF\le3m\beta+2\rho,&m\ge2.
--   \end{cases}$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MarkedPopulationConstraints.lean lines 56–86; SHA256 f2255606e47ba532d18007f98788f5695045e4edda1485b845e0f24bc605e854; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActiveSocketMacroGeometry
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkedSocketPopulation
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PairedPopulationConstraints
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
import Mathlib.Data.Nat.Choose.Basic
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
namespace SensitivityMarkedPopulationConstraints
end SensitivityMarkedPopulationConstraints
namespace SensitivityMarkedPseudoforestPopulation
end SensitivityMarkedPseudoforestPopulation
namespace SensitivityMarkedSocketPopulation
end SensitivityMarkedSocketPopulation
namespace SensitivityPairedPopulation
end SensitivityPairedPopulation
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! The explicit marked quadratic and pseudoforest inequalities used by the
finite paired-population checker, derived from actual guard incidences. -/
open SensitivityMarkedPopulationConstraints
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityActiveSocketGeometry SensitivityActiveSocketPopulation
open SensitivityMarkedSocketPopulation SensitivityMarkedPseudoforestPopulation
open SensitivityPairedPopulation
set_option autoImplicit false
variable {M B I Color : Type} {L : ℕ} [Fintype M] [Fintype B]

theorem SensitivityMarkedPopulationConstraints.actual_marker_forest
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (hinternal : CoversPairs internalArc) (hcovers : CoversPairs (pairedArc macroArc internalArc))
    (active : M × B → Bool) (candidates markers zeros : Finset (M × B))
    (hdisj : Disjoint candidates markers) (hzeros : zeros ⊆ candidates)
    (cutoff alpha beta residual : ℕ) (hm : 0 < markers.card)
    (x : (((M × B) × Bool) × I) → Bool)
    (hactive : ∀ v ∈ candidates, passes row cutoff (socketInput x (v, active v)))
    (hhigh : ∀ v ∈ markers, ∀ b, passes row cutoff (socketInput x (v, b)))
    (hbudget : ∀ v ∈ candidates,
      guardCount row (pairedTournamentGuards macroArc label internalArc) v cutoff x ≤ 1)
    (hzero : ∀ v ∈ zeros,
      guardCount row (pairedTournamentGuards macroArc label internalArc) v cutoff x = 0)
    (hresidual : (∑ v ∈ markers,
      (failedIntoCandidates row macroArc label internalArc candidates cutoff x v).card) ≤ residual)
    (hordinary : ∀ t ⊆ candidates, Independent macroArc label active t → t.card ≤ alpha)
    (hmarked : ∀ marker ∈ markers, ∀ t ⊆ candidates, Independent macroArc label active t →
      (∀ v ∈ t, CleanlyDominates macroArc label active marker.1 v) → t.card ≤ beta) :
    markerForest alpha beta (candidates.card + zeros.card) markers.card residual := by sorry
