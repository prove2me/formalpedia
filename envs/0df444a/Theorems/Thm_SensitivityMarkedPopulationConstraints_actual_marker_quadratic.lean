-- Prove2me | Theorems.Thm_SensitivityMarkedPopulationConstraints_actual_marker_quadratic
-- name    : SensitivityMarkedPopulationConstraints.actual_marker_quadratic
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:33:52.947126+00:00
-- url     : https://prove2.me/theorems/2762d96a-c532-4de3-9f75-2bd83aaeb3ac
-- title:
--   Marked quadratic constraint from actual guard incidences
-- statement:
--   Consider paired guards on the finite row set $V=M\times B$, a child Boolean family, a cutoff, and a fixed input. Choose an active side for each candidate row. Assume that the internal relation and the full paired relation cover every pair of distinct vertices. A candidate is cleanly dominated by a marker when the marker's macro has an arc to the candidate's macro whose label avoids the candidate's selected active side. Independence refers to the conflict graph determined by these selected sides. Let $C,H$ be disjoint. Selected candidate sides pass the cutoff, both sides of every marker pass it, and each candidate has at most $q$ active guards. Let positive integers $\alpha,\beta$ bound, respectively, all independent candidate subsets and the independent subsets cleanly dominated by any one marker. Suppose the total number of active marker-to-candidate checks is at most $\rho$. Put $N=|C|$ and $m=|H|$, and define
--
--   $$D=\max\{0,\ m\max\{0,N-(2q+1)\beta\}-\rho\}.$$
--
--   Then
--
--   $$N^2+2\alpha D\le\alpha(2q+1)N.$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MarkedPopulationConstraints.lean lines 18–54; SHA256 f2255606e47ba532d18007f98788f5695045e4edda1485b845e0f24bc605e854; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

theorem SensitivityMarkedPopulationConstraints.actual_marker_quadratic
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (hinternal : CoversPairs internalArc) (hcovers : CoversPairs (pairedArc macroArc internalArc))
    (active : M × B → Bool) (candidates markers : Finset (M × B))
    (hdisj : Disjoint candidates markers) (cutoff alpha beta q residual : ℕ)
    (ha : 0 < alpha) (hb : 0 < beta) (x : (((M × B) × Bool) × I) → Bool)
    (hactive : ∀ v ∈ candidates, passes row cutoff (socketInput x (v, active v)))
    (hhigh : ∀ v ∈ markers, ∀ b, passes row cutoff (socketInput x (v, b)))
    (hbudget : ∀ v ∈ candidates,
      guardCount row (pairedTournamentGuards macroArc label internalArc) v cutoff x ≤ q)
    (hresidual : (∑ v ∈ markers,
      (failedIntoCandidates row macroArc label internalArc candidates cutoff x v).card) ≤ residual)
    (hordinary : ∀ t ⊆ candidates, Independent macroArc label active t → t.card ≤ alpha)
    (hmarked : ∀ marker ∈ markers, ∀ t ⊆ candidates, Independent macroArc label active t →
      (∀ v ∈ t, CleanlyDominates macroArc label active marker.1 v) → t.card ≤ beta) :
    markerQuadratic alpha beta q candidates.card markers.card residual := by sorry
