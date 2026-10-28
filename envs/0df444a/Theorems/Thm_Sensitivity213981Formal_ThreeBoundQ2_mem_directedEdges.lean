-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundQ2_mem_directedEdges
-- name    : Sensitivity213981Formal.ThreeBoundQ2.mem_directedEdges
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:45:08.334934+00:00
-- url     : https://prove2.me/theorems/d7e7298f-c827-4af7-84b5-90653107418d
-- title:
--   The finite orientation encoding preserves every tournament edge
-- statement:
--   Let R be a tournament on the ordered vertex set Fin n. List each unordered pair once in increasing order and orient it according to the bit encoding of R. A directed pair (v,w) belongs to this list of directed edges if and only if R(v,w).
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Q2EnumerationBridge.lean, lines 93–115.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundQ2.mem_directedEdges :
∀ {n : Nat} (R : Fin n → Fin n → Prop) [inst : @DecidableRel.{1, 1} (Fin n) (Fin n) R]
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament (Fin n) R) (v w : Fin n),
  Iff
    (@Membership.mem.{0, 0} (Prod.{0, 0} (Fin n) (Fin n)) (List.{0} (Prod.{0, 0} (Fin n) (Fin n)))
      (@List.instMembership.{0} (Prod.{0, 0} (Fin n) (Fin n)))
      (@Sensitivity213981Formal.ThreeBoundQ2.directedEdges (Fin n) (Sensitivity213981Formal.ThreeBoundQ2.edges n)
        (@Sensitivity213981Formal.ThreeBoundQ2.orientationBits n R inst))
      (@Prod.mk.{0, 0} (Fin n) (Fin n) v w))
    (R v w) := by sorry
