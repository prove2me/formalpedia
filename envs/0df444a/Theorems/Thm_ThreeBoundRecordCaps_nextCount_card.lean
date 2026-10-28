-- Prove2me | Theorems.Thm_ThreeBoundRecordCaps_nextCount_card
-- name    : ThreeBoundRecordCaps.nextCount_card
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:44:37.581957+00:00
-- url     : https://prove2.me/theorems/e721d710-2c1b-47de-a14a-9510ceda9902
-- title:
--   The next-count field counts heads with budget at most q+1 outside a target prefix
-- statement:
--   Let H be a finite tagged head set and suppose a q≤2 record r stores its exact eight type counts. For every q, nextCount(r,q) equals the number of heads w∈H whose type is absent from positive prefix q and whose failed-guard budget is at most q+1.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, RecordCapStats, lines 41–55; source SHA256 ed833e3308d481a66dfa0991dfe1e540a9627d5a4f82a610e495716c925c454e.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_ActualKindFilters
import Definitions.Def_Sensitivity213303_ActualPrefixCaps
import Definitions.Def_Sensitivity213303_ActualTargetAccounting
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_CapAlgorithm
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_GlobalAccounting
import Definitions.Def_Sensitivity213303_GradedCandidates
import Definitions.Def_Sensitivity213303_GradedGlobalCover
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_HeadCostExpressions
import Definitions.Def_Sensitivity213303_HeadCosts
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_Q2EnumerationBridge
import Definitions.Def_Sensitivity213303_Q2RawExpressions
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace ThreeBoundAccounting
end ThreeBoundAccounting
namespace ThreeBoundCapAlgorithm
end ThreeBoundCapAlgorithm
namespace ThreeBoundNumeric
end ThreeBoundNumeric
namespace ThreeBoundTypeCounts
end ThreeBoundTypeCounts
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace ThreeBoundRecordCaps
end ThreeBoundRecordCaps
open ThreeBoundRecordCaps
open ThreeBoundNumeric ThreeBoundCapAlgorithm ThreeBoundAccounting ThreeBoundTypeCounts
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

theorem ThreeBoundRecordCaps.nextCount_card (H : Finset V) (tag : V → Fin 8) (x : Q2Record)
    (hx : ∀ k : Fin 8, x k.val = typeCount H tag k) (q : ℕ) :
    nextCount x q = (H.filter fun w =>
      ThreeBoundQ2.positivePrefix q (tag w) = false ∧ ThreeBoundQ2.budget (tag w) ≤ q+1).card := by sorry
