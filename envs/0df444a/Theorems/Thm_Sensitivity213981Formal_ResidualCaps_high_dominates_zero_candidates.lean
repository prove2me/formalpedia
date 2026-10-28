-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ResidualCaps_high_dominates_zero_candidates
-- name    : Sensitivity213981Formal.ResidualCaps.high_dominates_zero_candidates
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:33:47.769054+00:00
-- url     : https://prove2.me/theorems/0b222295-cb24-4e36-bac8-516bfdc3157d
-- title:
--   Every high vertex dominates every zero-failure candidate
-- statement:
--   Let \(A,H\) be disjoint finite vertex sets in a labeled tournament. Suppose both children of every vertex in \(H\) satisfy the guard predicate, while every vertex of \(A\) has zero failed guards. Then
--   \[
--   R(v,w)\qquad(v\in H,\ w\in A).
--   \]
--   This supplies the domination relation required for the zero-tolerance source and multi-dominator exclusions.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ResidualCaps.lean, lines 97–116.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ResidualCaps.high_dominates_zero_candidates :
∀ {V X : Type} [inst : Fintype.{0} V] [DecidableEq.{1} V] (R : V → V → Prop)
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R) (ell : V → V → Bool) (guard : X → Prop)
  (children : V → Bool → X) (A H : Finset.{0} V)
  (hdis : @Disjoint.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V) (@Finset.instOrderBot.{0} V) A H)
  (hhigh :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H w →
        ∀ (c : Bool), guard (children w c))
  (hzero :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) A v →
        @Eq.{1} Nat
          (@Finset.card.{0} V
            (@Sensitivity213981Formal.TournamentHighRows.guardFailures V X inst R ell guard children v))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (v : V),
  @Membership.mem.{0, 0} V (Finset.{0} V) (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
      H v →
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) A w →
        R v w := by sorry
