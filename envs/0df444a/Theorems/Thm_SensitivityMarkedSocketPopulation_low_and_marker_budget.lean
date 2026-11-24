-- Prove2me | Theorems.Thm_SensitivityMarkedSocketPopulation_low_and_marker_budget
-- name    : SensitivityMarkedSocketPopulation.low_and_marker_budget
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:33:54.947351+00:00
-- url     : https://prove2.me/theorems/8fdfdbd1-ad1c-4b1c-a04e-4a80719d7baa
-- title:
--   Candidate and high-marker incidences share the guard budget
-- statement:
--   Consider paired guards on a finite row set $V=M\times B$, a cutoff, and an input. Let $C,H\subseteq V$ be disjoint. Every candidate $w\in C$ has a selected side that passes the cutoff, and both sides of every marker $w\in H$ pass it. For every source row $v$,
--
--   $$|\{w\in C:\text{the check }v\to w\text{ contains the selected side of }w\}|
--   +|\{w\in H:v\to w\}|\le g(v),$$
--
--   where the first set also requires the paired arc $v\to w$, and $g(v)$ is the number of active guards at $v$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MarkedSocketPopulation.lean lines 45–77; SHA256 e054fe8e5123006085f22ef85c964ee16ac1d1a382c0d022de446fcd82af7807; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActiveSocketMacroGeometry
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkedSocketPopulation
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
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

theorem SensitivityMarkedSocketPopulation.low_and_marker_budget [Fintype M] [Fintype B]
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (active : M × B → Bool) (candidates markers : Finset (M × B))
    (hdisj : Disjoint candidates markers) (cutoff : ℕ)
    (x : (((M × B) × Bool) × I) → Bool)
    (hactive : ∀ w ∈ candidates, passes row cutoff (socketInput x (w, active w)))
    (hhigh : ∀ w ∈ markers, ∀ b, passes row cutoff (socketInput x (w, b))) (v : M × B) :
    (candidates.filter (DirectedConflict macroArc label internalArc active v)).card +
      (toMarkers (pairedArc macroArc internalArc) markers v).card ≤
      guardCount row (pairedTournamentGuards macroArc label internalArc) v cutoff x := by sorry
