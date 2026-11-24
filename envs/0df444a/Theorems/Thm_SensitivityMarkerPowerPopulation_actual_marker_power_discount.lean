-- Prove2me | Theorems.Thm_SensitivityMarkerPowerPopulation_actual_marker_power_discount
-- name    : SensitivityMarkerPowerPopulation.actual_marker_power_discount
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:34:04.362949+00:00
-- url     : https://prove2.me/theorems/4126801d-7beb-4c13-9320-983329ef72c0
-- title:
--   Integral population bound from copies indexed by marker subsets
-- statement:
--   Consider paired guards on the finite row set $V=M\times B$, a child Boolean family, a cutoff, and a fixed input. Choose an active side for each candidate row. Assume that the internal relation and the full paired relation cover every pair of distinct vertices. A candidate is cleanly dominated by a marker when the marker's macro has an arc to the candidate's macro whose label avoids the candidate's selected active side. Independence refers to the conflict graph determined by these selected sides. Let $C,H$ be disjoint, with $N=|C|>0$ and $h=|H|$. Selected candidate sides and both marker sides pass the cutoff. Fix $r\ge1$. For each $r$-element marker subset $J$, let $\alpha_J$ bound every independent candidate subset cleanly dominated by all markers in $J$, and suppose $\sum_{|J|=r}\alpha_J\le A_r$ with $A_r>0$. Let $\rho$ bound active marker-to-candidate incidences, let $T$ count candidate-to-marker arcs, and let $S$ be total candidate guard usage. Put
--
--   $$a=\max\{0,hN-T-\rho\},\qquad q=\lfloor a/N\rfloor,\qquad u=a\bmod N.$$
--
--   Then
--
--   $$E\!\left(N\binom qr+u\binom q{r-1},A_r\right)
--   +\binom hr T\le\binom hr S.$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MarkerPowerPopulation.lean lines 68–120; SHA256 7a463e07d51d543172edd4d015de959a99fbfdc46799fb681214dd03d594e52a; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActiveSocketMacroGeometry
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_IntegralGraphPopulation
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
import Mathlib.Data.Finset.Powerset
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
namespace SensitivityBalancedIncidence
end SensitivityBalancedIncidence
namespace SensitivityCopyGraphPopulation
end SensitivityCopyGraphPopulation
namespace SensitivityGraphPopulation
end SensitivityGraphPopulation
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityMarkedSocketPopulation
end SensitivityMarkedSocketPopulation
namespace SensitivityMarkerCopyPopulation
end SensitivityMarkerCopyPopulation
namespace SensitivityMarkerPowerPopulation
end SensitivityMarkerPowerPopulation
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! The single/pair/triple clean-marker intersection population inequalities. -/
open SensitivityMarkerPowerPopulation
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityActiveSocketGeometry SensitivityActiveSocketPopulation
open SensitivityGraphPopulation SensitivityMarkedSocketPopulation SensitivityCopyGraphPopulation
open SensitivityMarkerCopyPopulation SensitivityBalancedIncidence
set_option autoImplicit false
variable {M B I Color : Type} {L : ℕ}

theorem SensitivityMarkerPowerPopulation.actual_marker_power_discount [Fintype M] [Fintype B]
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (hinternal : CoversPairs internalArc) (hcovers : CoversPairs (pairedArc macroArc internalArc))
    (active : M × B → Bool) (candidates markers : Finset (M × B))
    (hdisj : Disjoint candidates markers) (cutoff k residual totalAlpha : ℕ)
    (alpha : Finset (M × B) → ℕ) (hpos : 0 < totalAlpha) (hn : 0 < candidates.card)
    (halpha : (∑ selected ∈ markers.powersetCard (k + 1), alpha selected) ≤ totalAlpha)
    (x : (((M × B) × Bool) × I) → Bool)
    (hactive : ∀ v ∈ candidates, passes row cutoff (socketInput x (v, active v)))
    (hhigh : ∀ v ∈ markers, ∀ b, passes row cutoff (socketInput x (v, b)))
    (hresidual : (∑ marker ∈ markers,
      (failedIntoCandidates row macroArc label internalArc candidates cutoff x marker).card) ≤ residual)
    (hcap : ∀ selected ∈ markers.powersetCard (k + 1), ∀ s ⊆ candidates,
      Independent macroArc label active s →
      (∀ marker ∈ selected, ∀ v ∈ s, CleanlyDominates macroArc label active marker.1 v) →
      s.card ≤ alpha selected) :
    let outgoing := ∑ v ∈ candidates, (toMarkers (pairedArc macroArc internalArc) markers v).card
    let appear := markers.card * candidates.card - outgoing - residual
    let base := appear / candidates.card
    let remainder := appear % candidates.card
    minimumEdges (candidates.card * base.choose (k + 1) + remainder * base.choose k) totalAlpha +
      markers.card.choose (k + 1) * outgoing ≤
      markers.card.choose (k + 1) * (∑ v ∈ candidates,
        guardCount row (pairedTournamentGuards macroArc label internalArc) v cutoff x) := by sorry
