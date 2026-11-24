-- Prove2me | Theorems.Thm_SensitivityMarkedSocketPopulation_candidate_marker_partition
-- name    : SensitivityMarkedSocketPopulation.candidate_marker_partition
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:34:10.255439+00:00
-- url     : https://prove2.me/theorems/89883501-a2ca-496e-9606-6a5858cf61f2
-- title:
--   Candidate decomposition relative to a marker
-- statement:
--   Consider paired guards and suppose the paired arc relation covers every pair of distinct rows. Fix a finite candidate set $C$ and a marker $h\notin C$. Let $C_{\mathrm{clean}}$ consist of candidates reached by $h$ whose check from $h$ is inactive, let $C_{\to h}$ consist of candidates with an arc to $h$, and let $C_{\mathrm{failed}}$ consist of candidates reached by $h$ whose check is active. Then
--
--   $$|C|\le|C_{\mathrm{clean}}|+|C_{\to h}|+|C_{\mathrm{failed}}|.$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MarkedSocketPopulation.lean lines 169–192; SHA256 e054fe8e5123006085f22ef85c964ee16ac1d1a382c0d022de446fcd82af7807; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkedSocketPopulation
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
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
namespace SensitivityGraphPopulation
end SensitivityGraphPopulation
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityMarkedSocketPopulation
end SensitivityMarkedSocketPopulation
namespace SensitivityPseudoforest
end SensitivityPseudoforest
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! Exact marker incidences and clean dominated candidate populations. -/
open SensitivityMarkedSocketPopulation
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityActiveSocketGeometry SensitivityActiveSocketPopulation
open SensitivityGraphPopulation SensitivityPseudoforest
set_option autoImplicit false
variable {V S M B I Color : Type} {L : ℕ}

theorem SensitivityMarkedSocketPopulation.candidate_marker_partition
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (hcovers : CoversPairs (pairedArc macroArc internalArc))
    (candidates : Finset (M × B)) (cutoff : ℕ)
    (x : (((M × B) × Bool) × I) → Bool) (marker : M × B) (hmarker : marker ∉ candidates) :
    candidates.card ≤
      (cleanCandidates row macroArc label internalArc candidates cutoff x marker).card +
      (candidates.filter fun v => pairedArc macroArc internalArc v marker).card +
      (failedIntoCandidates row macroArc label internalArc candidates cutoff x marker).card := by sorry
