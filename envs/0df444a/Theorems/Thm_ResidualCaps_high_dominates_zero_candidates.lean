-- Prove2me | Theorems.Thm_ResidualCaps_high_dominates_zero_candidates
-- name    : ResidualCaps.high_dominates_zero_candidates
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:42:00.15814+00:00
-- url     : https://prove2.me/theorems/ef4669b4-9855-43bd-94f3-feb11c2bd416
-- title:
--   Every high vertex dominates every zero-failure candidate
-- statement:
--   Let \(A,H\) be disjoint finite vertex sets in a labeled tournament. Suppose both children of every vertex in \(H\) satisfy the guard predicate, while every vertex of \(A\) has zero failed guards. Then
--   \[
--   R(v,w)\qquad(v\in H,\ w\in A).
--   \]
--   This supplies the domination relation required for the zero-tolerance source and multi-dominator exclusions.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ResidualCaps, lines 97–116; source SHA256 ec03db09ea4a2f3cbd1fc6c44684bdf2e0853b238640ccde652c9ebbdb8a911c.

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
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_TournamentHighRows

namespace CandidateCoherence
end CandidateCoherence
namespace GuardAugmentation
end GuardAugmentation
namespace TournamentHighRows
end TournamentHighRows
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ResidualCaps
end ResidualCaps
open ResidualCaps
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation
variable {V X : Type} [Fintype V] [DecidableEq V]

theorem ResidualCaps.high_dominates_zero_candidates (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (A H : Finset V) (hdis : Disjoint A H)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c))
    (hzero : ∀ v ∈ A, (guardFailures R ell guard children v).card = 0) :
    ∀ v ∈ H, ∀ w ∈ A, R v w := by sorry
