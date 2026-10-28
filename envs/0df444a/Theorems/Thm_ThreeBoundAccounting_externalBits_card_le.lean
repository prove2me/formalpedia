-- Prove2me | Theorems.Thm_ThreeBoundAccounting_externalBits_card_le
-- name    : ThreeBoundAccounting.externalBits_card_le
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:44:32.505421+00:00
-- url     : https://prove2.me/theorems/eabd6412-aa83-4a92-8f22-c16095fa428f
-- title:
--   External guard repairs are bounded by residual failed-guard counts
-- statement:
--   Let G be a set of guard sources and H a set of high heads, whose two children accept at the strong guard level. Suppose each actual failed guard of a source in G also accepts at the weak guard level, and the child B bound between these guard levels is s. The union of guard-repair bits at heads outside H has size at most s∑_{v∈G} (|failed(v)|−|H∩out(v)|).
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, GlobalAccounting, lines 164–192; source SHA256 8368f847d33d41b253e3289693d4dc50d871ab3b4b05626890fae7d30bb69fc4.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
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
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GlobalAccounting
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_ResidualCaps
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
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace ThreeBoundAccounting
end ThreeBoundAccounting
open ThreeBoundAccounting
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical BigOperators
variable {V I K : Type} [Fintype V] [Fintype I] [Fintype K]
variable {L : Type} [Preorder L]

theorem ThreeBoundAccounting.externalBits_card_le (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (i j : L) (x : ((V × Bool) × I) → Bool) (G H : Finset V)
    (hH : ∀ w ∈ H, ∀ c : Bool, F (S.guard j) (child x w c) = true)
    (hweak : ∀ v ∈ G, ∀ w ∈ failed S F j x v,
      F (S.guard i) (child x w (S.label v w)) = true)
    (s : ℕ) (hs : BBound F (S.guard j) (S.guard i) s) :
    (externalBits S F j x G H).card ≤
      (∑ v ∈ G, ((failed S F j x v).card-(H.filter (S.Adj v)).card))*s := by sorry
