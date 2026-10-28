-- Prove2me | Theorems.Thm_ResidualCaps_cleaned_marked_zero
-- name    : ResidualCaps.cleaned_marked_zero
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:42:07.904681+00:00
-- url     : https://prove2.me/theorems/26842634-7f95-4eb7-ad55-62835d8d5fe4
-- title:
--   Cleaning marker mismatches produces a zero-budget marked configuration
-- statement:
--   Let \(A,H\) be disjoint vertex sets in a labeled tournament, and let \(M\subseteq H\) with \(|M|\le q+2\). Each candidate in \(A\) has a designated color whose partner child is guard-true; both children of vertices in \(H\) are guard-true. Suppose candidates have at most \(q\) actual guard failures. Delete from \(A\) every head that mismatches any selected marker, obtaining \(C\). Then
--   \[
--   \operatorname{MarkedGood}(C,M,q,0)
--   \]
--   holds for the given coloring. The selected markers may have larger global failure budgets; only their number is needed here.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ResidualCaps, lines 165–193; source SHA256 ec03db09ea4a2f3cbd1fc6c44684bdf2e0853b238640ccde652c9ebbdb8a911c.

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

theorem ResidualCaps.cleaned_marked_zero (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (A H M : Finset V) (hdis : Disjoint A H) (hMH : M ⊆ H)
    (color : V → Bool) (q : ℕ) (hsize : M.card ≤ q+2)
    (hpartner : ∀ w ∈ A, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c))
    (hbudget : ∀ v ∈ A, (guardFailures R ell guard children v).card ≤ q) :
    MarkedGood R ell (cleanedHeads R ell A M color) M q 0 color := by sorry
