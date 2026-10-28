-- Prove2me | Theorems.Thm_ThreeBoundGradedCandidates_target_missing_weak_false
-- name    : ThreeBoundGradedCandidates.target_missing_weak_false
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:42:20.245668+00:00
-- url     : https://prove2.me/theorems/4d4f9d1d-ef2b-482d-ab1a-04f3e01bd751
-- title:
--   A graded candidate's missing child fails the weak same-tier threshold
-- statement:
--   Consider a matched weak/strong graded pair on a nested Boolean family, and suppose the weak parent is false. Let a row have exactly \(b\) strong guard failures, within the strong tolerance. If its partner child passes the strong threshold at \(b\), then the designated child satisfies
--   \[
--   F_{\mathrm{weak}(b)}(x_{v,c})=\mathrm{false}.
--   \]
--   This gives the weak-false hypothesis for charging a strong target repair to a conditional child profile.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, GradedCandidates, lines 60–79; source SHA256 b678c8d2d17ede20517cee0be5f70571b803e9e5a8ee20483d5fef6346a7243d.

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

theorem ThreeBoundGradedCandidates.target_missing_weak_false (hoff : parent S F i x = false)
    (v : V) (b : ℕ) (c : Bool) (hb : b ≤ S.tolerance j)
    (hc : (failed S F j x v).card = b)
    (hpartner : F (P.strong b) (child x v (!c)) = true) :
    F (P.weak b) (child x v c) = false := by sorry
