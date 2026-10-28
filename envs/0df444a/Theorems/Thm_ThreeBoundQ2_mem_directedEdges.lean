-- Prove2me | Theorems.Thm_ThreeBoundQ2_mem_directedEdges
-- name    : ThreeBoundQ2.mem_directedEdges
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:43:24.780965+00:00
-- url     : https://prove2.me/theorems/e1ddccf4-768e-45e3-803e-290b8a792868
-- title:
--   The finite orientation encoding preserves every tournament edge
-- statement:
--   Let R be a tournament on the ordered vertex set Fin n. List each unordered pair once in increasing order and orient it according to the bit encoding of R. A directed pair (v,w) belongs to this list of directed edges if and only if R(v,w).
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, Q2EnumerationBridge, lines 93–115; source SHA256 03a4fb36b007fff28d4e49eea18e6afba235c6589b867de536205b797b906503.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_Q2EnumerationBridge
import Definitions.Def_Sensitivity213303_TournamentHighRows


set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ThreeBoundQ2
end ThreeBoundQ2
open ThreeBoundQ2
open scoped Classical BigOperators

theorem ThreeBoundQ2.mem_directedEdges {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (hR : TournamentHighRows.IsTournament R) (v w : Fin n) :
    (v,w) ∈ directedEdges (edges n) (orientationBits R) ↔ R v w := by sorry
