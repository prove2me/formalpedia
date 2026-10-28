-- Prove2me | Theorems.Thm_ThreeBoundActualKindFilters_kind_positive_only
-- name    : ThreeBoundActualKindFilters.kind_positive_only
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:44:16.942244+00:00
-- url     : https://prove2.me/theorems/0398a6de-9f3d-4543-aa9d-4f1c8e858909
-- title:
--   Kinds zero, one and two identify positive-only heads and their exact failure count
-- statement:
--   If the actual child states of a head satisfy the q≤2 classification OfKind for a kind k≤2, then the head is a target candidate, is not a guard candidate, and has exactly k failed guards.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ActualKindFilters, lines 32–58; source SHA256 598b6c51ded9802b69c6a5a16a7156e5bb0257892c4b379809994981b3c297a0.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
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
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_ActualKindFilters
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_FullProfileClosure
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
import Definitions.Def_Sensitivity213303_Q2RawExpressions
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundActualHeadCosts
end ThreeBoundActualHeadCosts
namespace ThreeBoundAllKindHeadCosts
end ThreeBoundAllKindHeadCosts
namespace ThreeBoundFullProfile
end ThreeBoundFullProfile
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
namespace ThreeBoundGradedCover
end ThreeBoundGradedCover
namespace ThreeBoundHeadCharge
end ThreeBoundHeadCharge
namespace ThreeBoundHeadExpressions
end ThreeBoundHeadExpressions
namespace ThreeBoundNumeric
end ThreeBoundNumeric
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundActualKindFilters
end ThreeBoundActualKindFilters
open ThreeBoundActualKindFilters
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundHeadExpressions ThreeBoundAllKindHeadCosts ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem ThreeBoundActualKindFilters.kind_positive_only
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (t : ℕ → Fin n) (j : Fin n) (x : ((V × Bool) × I) → Bool) (w : V) (kind : Fin 8)
    (hk : Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
      (fun k z => F (t k) z = true) (S.tolerance j) (failed S F j x w).card
      (child x w false) (child x w true) kind)
    (hp : kind.val ≤ 2) :
    targetAt S F t j x w ∧ ¬ guardAt S F t j x w ∧ (failed S F j x w).card = kind.val := by sorry
