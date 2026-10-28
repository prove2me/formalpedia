-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundQ2_outCount_orientation_eq_card
-- name    : Sensitivity213981Formal.ThreeBoundQ2.outCount_orientation_eq_card
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:56:37.549658+00:00
-- url     : https://prove2.me/theorems/ffb5597a-de52-405b-b05b-4261447b419d
-- title:
--   Encoded outdegree equals the actual tournament outdegree
-- statement:
--   For any tournament R on Fin n and vertex v, the outCount computed from its orientation-bit list equals the cardinality of the set of vertices w satisfying R(v,w).
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Q2EnumerationBridge.lean, lines 136–154.

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

theorem Sensitivity213981Formal.ThreeBoundQ2.outCount_orientation_eq_card :
∀ {n : Nat} (R : Fin n → Fin n → Prop) [inst : @DecidableRel.{1, 1} (Fin n) (Fin n) R]
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament (Fin n) R) (v : Fin n),
  @Eq.{1} Nat
    (@Sensitivity213981Formal.ThreeBoundQ2.outCount (Fin n) (instDecidableEqFin n)
      (Sensitivity213981Formal.ThreeBoundQ2.edges n) (@Sensitivity213981Formal.ThreeBoundQ2.orientationBits n R inst) v)
    (@Finset.card.{0} (Fin n) (@Finset.filter.{0} (Fin n) (R v) (inst v) (@Finset.univ.{0} (Fin n) (Fin.fintype n)))) := by sorry
