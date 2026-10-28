-- Prove2me | Theorems.Thm_Q2CandidateTypes_pure_guard_next_both_false
-- name    : Q2CandidateTypes.pure_guard_next_both_false
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:40:06.514419+00:00
-- url     : https://prove2.me/theorems/ddc70171-ad54-47bd-afa1-8da17eeae637
-- title:
--   A pure lower guard candidate fails both next-level targets
-- statement:
--   Suppose \(b+1\le Q\), every target predicate through \(Q\) implies the guard predicate, and a pair of children is a guard candidate at level \(b\). Assume it is neither an accepted row nor a positive candidate at level \(b+1\). Then
--   \[
--   \neg\operatorname{target}_{b+1}(x)\quad\text{and}\quad
--   \neg\operatorname{target}_{b+1}(y).
--   \]
--   This identifies the stronger child interval available for a pure lower-guard head.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, Q2CandidateTypes, lines 169–192; source SHA256 7e8db07c231331862a069853ead1b29e5e7fab51f5c60add93e739c5f3441575.

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

theorem Q2CandidateTypes.pure_guard_next_both_false (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d b : ℕ) (x y : X) (hbQ : b+1 ≤ Q)
    (hgt : ∀ c, c ≤ Q → ∀ z, target c z → guard z)
    (hg : GuardCandidate target Q d b x y)
    (hp : ¬ PositiveCandidate guard target Q d (b+1) x y)
    (hno : ¬ Accepted target Q d x y) :
    ¬ target (b+1) x ∧ ¬ target (b+1) y := by sorry
