-- Prove2me | Theorems.Thm_SensitivityMarkerCopyPopulation_actual_marker_copy_discount
-- name    : SensitivityMarkerCopyPopulation.actual_marker_copy_discount
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:33:56.710244+00:00
-- url     : https://prove2.me/theorems/05bd6111-2658-4f5f-bf71-e23062a360a1
-- title:
--   Integral marker-copy bound with a residual allowance
-- statement:
--   Consider paired guards on the finite row set $V=M\times B$, a child Boolean family, a cutoff, and a fixed input. Choose an active side for each candidate row. Assume that the internal relation and the full paired relation cover every pair of distinct vertices. A candidate is cleanly dominated by a marker when the marker's macro has an arc to the candidate's macro whose label avoids the candidate's selected active side. Independence refers to the conflict graph determined by these selected sides. Let $C,H$ be disjoint, with $N=|C|$ and $m=|H|>0$. Selected candidate sides and both marker sides pass the cutoff. Suppose every independent candidate subset cleanly dominated by a marker has size at most $\beta>0$, and the total active marker-to-candidate incidence count is at most $\rho$. Let $S$ be total candidate guard usage, and put
--
--   $$a=\max\{0,mN-\rho\},\qquad b=\max\{0,a-(m+1)m\beta\}.$$
--
--   Then, writing $E$ for the integral minimum-edge function,
--
--   $$mb+E(a-b,m\beta)\le mS.$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MarkerCopyPopulation.lean lines 129–161; SHA256 f8be5a4f8d4aa837ce8c5191f7a065b7165ae3fd0c63f982711de3b9cb193303; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! Integral bounds for all clean-marker copies of the actual low conflict graph. -/
open SensitivityMarkerCopyPopulation
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityActiveSocketGeometry SensitivityActiveSocketPopulation
open SensitivityGraphPopulation SensitivityMarkedSocketPopulation SensitivityCopyGraphPopulation
set_option autoImplicit false
variable {M B I Color : Type} {L : ℕ}

theorem SensitivityMarkerCopyPopulation.actual_marker_copy_discount [Fintype M] [Fintype B]
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (hinternal : CoversPairs internalArc) (hcovers : CoversPairs (pairedArc macroArc internalArc))
    (active : M × B → Bool) (candidates markers : Finset (M × B))
    (hdisj : Disjoint candidates markers) (cutoff beta residual : ℕ)
    (hbeta : 0 < beta) (hmarks : markers.Nonempty)
    (x : (((M × B) × Bool) × I) → Bool)
    (hactive : ∀ v ∈ candidates, passes row cutoff (socketInput x (v, active v)))
    (hhigh : ∀ v ∈ markers, ∀ b, passes row cutoff (socketInput x (v, b)))
    (hresidual : (∑ marker ∈ markers,
      (failedIntoCandidates row macroArc label internalArc candidates cutoff x marker).card) ≤ residual)
    (hcap : ∀ marker ∈ markers, ∀ s ⊆ candidates, Independent macroArc label active s →
      (∀ v ∈ s, CleanlyDominates macroArc label active marker.1 v) → s.card ≤ beta) :
    let size := markers.card * candidates.card - residual
    let best := size - (markers.card + 1) * (markers.card * beta)
    markers.card * best + minimumEdges (size - best) (markers.card * beta) ≤
      markers.card * (∑ v ∈ candidates,
        guardCount row (pairedTournamentGuards macroArc label internalArc) v cutoff x) := by sorry
