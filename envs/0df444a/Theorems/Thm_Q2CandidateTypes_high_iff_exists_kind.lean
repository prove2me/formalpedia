-- Prove2me | Theorems.Thm_Q2CandidateTypes_high_iff_exists_kind
-- name    : Q2CandidateTypes.high_iff_exists_kind
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:39:57.739986+00:00
-- url     : https://prove2.me/theorems/b1355584-b97f-4b9d-aab0-2eb13a117ffb
-- title:
--   Eight types exhaust the high candidates for tolerances at most two
-- statement:
--   Let \(Q\le2\), let \(d\) be a guard-failure count, and fix two children with a guard predicate and target predicates indexed by natural numbers. Then
--   \[
--   \operatorname{High}(Q,d,x,y)
--   \quad\Longleftrightarrow\quad
--   \exists k\in\operatorname{Fin}(8),\ \operatorname{OfKind}(Q,d,x,y,k).
--   \]
--   The eight types distinguish positive candidates at levels \(0,1,2\), pure guard candidates at levels \(0,1,2\), and the two possible positive/guard overlaps. This supplies the exhaustive type classification for the \(q\le2\) table.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, Q2CandidateTypes, lines 97–125; source SHA256 7e8db07c231331862a069853ead1b29e5e7fab51f5c60add93e739c5f3441575.

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

theorem Q2CandidateTypes.high_iff_exists_kind (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (hQ : Q ≤ 2) (x y : X) :
    High guard target Q d x y ↔ ∃ k : Fin 8, OfKind guard target Q d x y k := by sorry
