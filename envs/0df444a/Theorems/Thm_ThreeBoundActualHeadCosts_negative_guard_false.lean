-- Prove2me | Theorems.Thm_ThreeBoundActualHeadCosts_negative_guard_false
-- name    : ThreeBoundActualHeadCosts.negative_guard_false
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:43:44.016006+00:00
-- url     : https://prove2.me/theorems/5a4aa1ca-f3d6-451b-b626-af6c8762b99b
-- title:
--   A negative target has a false guard at its missing child
-- statement:
--   For an actual negative target in the graded candidate construction, its designated missing child is false at the strong guard level.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ActualHeadCosts, lines 41–53; source SHA256 a66d58d8ea25978ac8f19433350b0fb930a74053dcbb642a8fdac2b6ddf28781.

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
import Definitions.Def_Sensitivity213303_GradedGlobalCover
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
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
namespace ThreeBoundGradedCover
end ThreeBoundGradedCover
namespace ThreeBoundHeadCharge
end ThreeBoundHeadCharge
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace ThreeBoundActualHeadCosts
end ThreeBoundActualHeadCosts
open ThreeBoundActualHeadCosts
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover
open scoped Classical BigOperators
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]
variable (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
  (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
include hF P

theorem ThreeBoundActualHeadCosts.negative_guard_false (w : V) (hw : w ∈ negativeTargets S F P.strong j x) :
    F (S.guard j) (child x w (missing S F P.strong j x w)) = false := by sorry
