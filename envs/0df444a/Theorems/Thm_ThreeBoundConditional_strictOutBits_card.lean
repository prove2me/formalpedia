-- Prove2me | Theorems.Thm_ThreeBoundConditional_strictOutBits_card
-- name    : ThreeBoundConditional.strictOutBits_card
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:44:04.413857+00:00
-- url     : https://prove2.me/theorems/731258c8-3727-4df1-9c2a-66f59b3ff06b
-- title:
--   A one-marker exclusion bound controls outgoing strict repairs
-- statement:
--   Let a zero-tolerance row p accept at target t_j and guard g_j. Assume g_j≤t_l and g_l≤t_l, a one-marker dominator exclusion threshold cap+1, and a child bound A(g_j,t_l)≤a. The union of strict repairs to candidate rows outgoing from p, with target t_l and guard g_l, has cardinality at most cap·a.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, StrictPositive, lines 80–97; source SHA256 549e6ba1808bd229a847f779827b54a74eae41146d2a38e7d8ed2b2cf1b42923.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_ConditionalOrdinary
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_StrictPositive
import Definitions.Def_Sensitivity213303_StrictUnion
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace ThreeBoundConditional
end ThreeBoundConditional
open ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem ThreeBoundConditional.strictOutBits_card (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (tj gj tl gl : L)
    (hgt : gj ≤ tl) (hglt : gl ≤ tl)
    (x : ((V × Bool) × I) → Bool) (p : V) (hp : ordinaryRow S F tj gj 0 x p)
    (cap a : ℕ) (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (cap+1))
    (ha : ABound F gj tl a) : (strictOutBits S F tl gl x p).card ≤ cap*a := by sorry
