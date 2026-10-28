-- Prove2me | Theorems.Thm_ThreeBoundTagPrefixes_kind_target_prefix_iff
-- name    : ThreeBoundTagPrefixes.kind_target_prefix_iff
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:45:44.28023+00:00
-- url     : https://prove2.me/theorems/e10b2deb-6c0e-41a8-889e-097b28222dac
-- title:
--   A head type determines exact target-prefix membership
-- statement:
--   Let F be nested and P be a valid weak–strong stage pair whose strong tolerance is at most two. Suppose head w at input x has actual high-head type κ among the eight q≤2 types. For every prefix index q, w belongs to the actual target-candidate prefix through q if and only if the type-level predicate positivePrefix(q,κ) is true.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, TagPrefixFacts, lines 16–65; source SHA256 37625d9efa0163c9bb1fb859d5eaf3ee7862e3f1aac96302868f475f4bb1c04d.

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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_ActualKindFilters
import Definitions.Def_Sensitivity213303_ActualPrefixCaps
import Definitions.Def_Sensitivity213303_ActualTargetAccounting
import Definitions.Def_Sensitivity213303_CandidateCoherence
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

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundActualHeadCosts
end ThreeBoundActualHeadCosts
namespace ThreeBoundActualTargets
end ThreeBoundActualTargets
namespace ThreeBoundAllKindHeadCosts
end ThreeBoundAllKindHeadCosts
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
namespace ThreeBoundGradedCover
end ThreeBoundGradedCover
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace ThreeBoundTagPrefixes
end ThreeBoundTagPrefixes
open ThreeBoundTagPrefixes
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundGradedCandidates
open ThreeBoundGradedCover ThreeBoundActualHeadCosts ThreeBoundAllKindHeadCosts
open ThreeBoundActualTargets
open scoped Classical BigOperators
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem ThreeBoundTagPrefixes.kind_target_prefix_iff
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤ 2) (w : V) (kind : Fin 8)
    (hk : Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
      (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
      (child x w false) (child x w true) kind) (q : ℕ) :
    w ∈ targetPrefix S F P.strong j x q ↔ ThreeBoundQ2.positivePrefix q kind = true := by sorry
