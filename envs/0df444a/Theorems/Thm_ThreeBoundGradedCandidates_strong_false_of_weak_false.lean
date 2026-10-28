-- Prove2me | Theorems.Thm_ThreeBoundGradedCandidates_strong_false_of_weak_false
-- name    : ThreeBoundGradedCandidates.strong_false_of_weak_false
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:42:11.511743+00:00
-- url     : https://prove2.me/theorems/d3c3585e-c5e2-46bf-9a97-d68389de7826
-- title:
--   Matched graded parents preserve weak-to-strong rejection
-- statement:
--   Let a matched pair of graded entries act on a nested Boolean family, with the ordered guards, target thresholds, and tolerances required by the pair data. Then
--   \[
--   \operatorname{parent}_i(x)=\mathrm{false}
--   \ \Longrightarrow\
--   \operatorname{parent}_j(x)=\mathrm{false},
--   \]
--   where \(i\) is the weak entry and \(j\) the strong entry. This permits strong repair covers to be used under a weak-false profile condition.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, GradedCandidates, lines 45–58; source SHA256 b678c8d2d17ede20517cee0be5f70571b803e9e5a8ee20483d5fef6346a7243d.

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

theorem ThreeBoundGradedCandidates.strong_false_of_weak_false (hoff : parent S F i x = false) :
    parent S F j x = false := by sorry
