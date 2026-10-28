-- Prove2me | Theorems.Thm_Q2CandidateTypes_actual_high_budget_sum_bound
-- name    : Q2CandidateTypes.actual_high_budget_sum_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:39:47.375278+00:00
-- url     : https://prove2.me/theorems/aeb9f6ed-632f-4419-a0a6-188d75d461ce
-- title:
--   Actual high vertices satisfy the global tournament budget
-- statement:
--   Let \(R\) be a tournament with two children at each vertex. Assume every target predicate through level \(Q\) implies the guard predicate. Let \(H\) be the actual high-vertex set, and assign each of its vertices one of the eight \(q\le2\) types so that its failed-guard count equals the type budget \(b(v)\). Then
--   \[
--   |H|(|H|-1)\le2\sum_{v\in H}b(v).
--   \]
--   This proves the global degree restriction used by the executable type enumeration from the actual Boolean configuration.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, Q2CandidateTypes, lines 279–301; source SHA256 7e8db07c231331862a069853ead1b29e5e7fab51f5c60add93e739c5f3441575.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_TournamentHighRows

namespace TournamentHighRows
end TournamentHighRows
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Q2CandidateTypes
end Q2CandidateTypes
open Q2CandidateTypes
open scoped Classical
open TournamentHighRows
variable {X V : Type}
variable [Fintype V]

theorem Q2CandidateTypes.actual_high_budget_sum_bound (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (target : ℕ → X → Prop)
    (Q : ℕ) (children : V → Bool → X)
    (hgt : ∀ b, b ≤ Q → ∀ z, target b z → guard z)
    (tag : V → Fin 8)
    (hcount : ∀ v ∈ highRows R ell guard target Q children,
      (guardFailures R ell guard children v).card = budget (tag v)) :
    let H := highRows R ell guard target Q children
    H.card * (H.card-1) ≤ 2 * ∑ v ∈ H, ThreeBoundQ2.budget (tag v) := by sorry
