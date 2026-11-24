-- Prove2me | Theorems.Thm_SensitivityActualGradedMarkerConstraints_actual_power_constraints
-- name    : SensitivityActualGradedMarkerConstraints.actual_power_constraints
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:33:55.193914+00:00
-- url     : https://prove2.me/theorems/aeeb1d63-501c-415b-8b9d-2028aaa6b031
-- title:
--   A common outgoing allowance satisfies all three marker-power bounds
-- statement:
--   Consider paired guards on the finite row set $V=M\times B$, a child Boolean family, a cutoff, and a fixed input. Choose an active side for each candidate row. Assume that the internal relation and the full paired relation cover every pair of distinct vertices. A candidate is cleanly dominated by a marker when the marker's macro has an arc to the candidate's macro whose label avoids the candidate's selected active side. Independence refers to the conflict graph determined by these selected sides. Let $C,H$ be disjoint, with selected candidate sides and both marker sides passing the cutoff. Let $N=|C|$, $h=|H|$, and $S$ be total candidate guard usage. Suppose a residual bound $\rho$ controls active marker-to-candidate incidences, and for each $r=1,2,3$ with $r\le h$ there are clean-domination independence caps whose sum is at most a positive $A_r$. Then there is a single integer $T$ with $0\le T\le S$ that satisfies every corresponding power inequality
--
--   $$E(C_r,A_r)+\binom hr T\le\binom hr S.$$
--
--   For $N>0$, write $a=\max\{0,hN-T-\rho\}$ and set
--   $$C_r=N\binom{\lfloor a/N\rfloor}{r}+(a\bmod N)\binom{\lfloor a/N\rfloor}{r-1};$$
--   for $N=0$, set $C_r=0$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/ActualGradedMarkerConstraints.lean lines 101–138; SHA256 c6b863f6bb368c56d93a884b3719f59fc7e1bf2847ac6e1a03b08f2f8746513a; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActiveSocketMacroGeometry
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkedSocketPopulation
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PairedPopulationConstraints
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentGuardCoverage
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace Sensitivity213981Formal.TournamentHighRows
end Sensitivity213981Formal.TournamentHighRows
namespace SensitivityActiveSocketGeometry
end SensitivityActiveSocketGeometry
namespace SensitivityActiveSocketPopulation
end SensitivityActiveSocketPopulation
namespace SensitivityActualGradedMarkerConstraints
end SensitivityActualGradedMarkerConstraints
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityMarkedIntegralPrefix
end SensitivityMarkedIntegralPrefix
namespace SensitivityMarkedPopulationConstraints
end SensitivityMarkedPopulationConstraints
namespace SensitivityMarkedSocketPopulation
end SensitivityMarkedSocketPopulation
namespace SensitivityMarkerCopyPopulation
end SensitivityMarkerCopyPopulation
namespace SensitivityMarkerPowerPopulation
end SensitivityMarkerPowerPopulation
namespace SensitivityPairedPopulation
end SensitivityPairedPopulation
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! Actual semantic forms of every integral, marked, and power constraint in
the graded population checker. The power orders share the same outgoing count. -/
open SensitivityActualGradedMarkerConstraints
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityActiveSocketGeometry SensitivityActiveSocketPopulation
open SensitivityMarkedSocketPopulation SensitivityMarkedIntegralPrefix
open SensitivityMarkerCopyPopulation SensitivityMarkerPowerPopulation
open SensitivityMarkedPopulationConstraints SensitivityPairedPopulation
open Sensitivity213981Formal.TournamentHighRows
set_option autoImplicit false
variable {M B I Color : Type} {L : ℕ} [Fintype M] [Fintype B]

theorem SensitivityActualGradedMarkerConstraints.actual_power_constraints
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (hinternal : CoversPairs internalArc) (hcovers : CoversPairs (pairedArc macroArc internalArc))
    (active : M × B → Bool) (candidates markers : Finset (M × B))
    (hdisj : Disjoint candidates markers) (cutoff : ℕ) (data : PowerData)
    (hheads : data.heads = markers.card) (alpha : Finset (M × B) → ℕ)
    (hpos : ∀ order : Fin 3, order.val+1 ≤ data.heads → 0 < data.alphaSum order)
    (halpha : ∀ order : Fin 3, order.val+1 ≤ data.heads →
      (∑ selected ∈ markers.powersetCard (order.val+1), alpha selected) ≤ data.alphaSum order)
    (x : (((M × B) × Bool) × I) → Bool)
    (hactive : ∀ v ∈ candidates, passes row cutoff (socketInput x (v,active v)))
    (hhigh : ∀ v ∈ markers, ∀ b, passes row cutoff (socketInput x (v,b)))
    (hresidual : (∑ v ∈ markers,
      (failedIntoCandidates row macroArc label internalArc candidates cutoff x v).card) ≤ data.residual)
    (hcap : ∀ order : Fin 3, order.val+1 ≤ data.heads →
      ∀ selected ∈ markers.powersetCard (order.val+1), ∀ t ⊆ candidates,
      Independent macroArc label active t →
      (∀ marker ∈ selected, ∀ v ∈ t, CleanlyDominates macroArc label active marker.1 v) →
      t.card ≤ alpha selected) :
    powerConstraints data candidates.card
      (∑ v ∈ candidates, guardCount row (pairedTournamentGuards macroArc label internalArc) v cutoff x) := by sorry
