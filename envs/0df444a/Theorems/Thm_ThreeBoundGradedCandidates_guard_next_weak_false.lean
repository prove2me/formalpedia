-- Prove2me | Theorems.Thm_ThreeBoundGradedCandidates_guard_next_weak_false
-- name    : ThreeBoundGradedCandidates.guard_next_weak_false
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:42:12.272909+00:00
-- url     : https://prove2.me/theorems/6d447259-97c3-4941-8d39-274592998cee
-- title:
--   A false weak parent forces a failed next-tier child
-- statement:
--   For a matched weak/strong graded pair built from a nested family, suppose the weak parent is false. If a row has \(b+1\) strong guard failures and this count is within the weak tolerance, then at least one of its two children fails the weak threshold at tier \(b+1\):
--   \[
--   F_{\mathrm{weak}(b+1)}(x_{v,0})=\mathrm{false}
--   \quad\text{or}\quad
--   F_{\mathrm{weak}(b+1)}(x_{v,1})=\mathrm{false}.
--   \]
--   This supplies the additional interval condition in the pure lower-guard head cost.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, GradedCandidates, lines 123–138; source SHA256 b678c8d2d17ede20517cee0be5f70571b803e9e5a8ee20483d5fef6346a7243d.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GradedCandidates
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_HeadCosts
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundRepair
end ThreeBoundRepair
namespace ThreeBoundWitness
end ThreeBoundWitness
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
open ThreeBoundGradedCandidates
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundRepair
open scoped Classical
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]
variable (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
  (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
include hF P

theorem ThreeBoundGradedCandidates.guard_next_weak_false (hoff : parent S F i x = false)
    (v : V) (b : ℕ) (hc : (failed S F j x v).card = b+1)
    (hb : b+1 ≤ S.tolerance i) :
    F (P.weak (b+1)) (child x v false) = false ∨
      F (P.weak (b+1)) (child x v true) = false := by sorry
