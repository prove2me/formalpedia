-- Prove2me | Theorems.Thm_Q2CandidateTypes_actual_positive_prefix_card_bound
-- name    : Q2CandidateTypes.actual_positive_prefix_card_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:39:58.296815+00:00
-- url     : https://prove2.me/theorems/08651114-221a-4cbe-9516-b1ab609279c2
-- title:
--   Actual positive type prefixes have sizes at most 1, 3, and 5
-- statement:
--   Under the tournament, target-to-guard implication, and exact type-budget hypotheses for the actual high set \(H\), let \(H_{\le q}\) consist of vertices whose assigned positive type lies in the prefix through \(q\). Then, for every natural number \(q\),
--   \[
--   |H_{\le q}|\le2q+1.
--   \]
--   In particular, the \(q=0,1,2\) prefixes have sizes at most \(1,3,5\). These are the semantic sources of the prefix restrictions in the finite enumerator.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, Q2CandidateTypes, lines 253–277; source SHA256 7e8db07c231331862a069853ead1b29e5e7fab51f5c60add93e739c5f3441575.

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

theorem Q2CandidateTypes.actual_positive_prefix_card_bound (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (target : ℕ → X → Prop)
    (Q : ℕ) (children : V → Bool → X)
    (hgt : ∀ b, b ≤ Q → ∀ z, target b z → guard z)
    (tag : V → Fin 8)
    (hcount : ∀ v ∈ highRows R ell guard target Q children,
      (guardFailures R ell guard children v).card = budget (tag v)) (q : ℕ) :
    ((highRows R ell guard target Q children).filter
      fun v => ThreeBoundQ2.positivePrefix q (tag v) = true).card ≤ 2*q+1 := by sorry
