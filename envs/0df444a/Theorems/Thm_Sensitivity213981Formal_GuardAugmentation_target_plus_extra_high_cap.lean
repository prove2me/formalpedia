-- Prove2me | Theorems.Thm_Sensitivity213981Formal_GuardAugmentation_target_plus_extra_high_cap
-- name    : Sensitivity213981Formal.GuardAugmentation.target_plus_extra_high_cap
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:35:02.781997+00:00
-- url     : https://prove2.me/theorems/483174b5-d2e6-4437-9f41-caa2e92b9340
-- title:
--   A one-extra-failure high set sharpens the target-prefix bound
-- statement:
--   Let \(C,G\) be disjoint sets in a labeled tournament. Each vertex of \(C\) has a designated color whose other child satisfies a guard predicate, while both children of every vertex in \(G\) satisfy it. Assume actual failed-guard counts are at most \(q\) on \(C\) and \(q+1\) on \(G\). If ordinary coherent sets at tolerance \(q\) have size less than \(a\), then
--   \[
--   |C|+|G|\le a.
--   \]
--   This is the strengthened prefix cap that includes high vertices with one additional allowed failure.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; GuardAugmentation.lean, lines 199–222.

import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_CandidateCoherence
import Definitions.Def_Sensitivity213981Formal_TournamentHighRows
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.GuardAugmentation.target_plus_extra_high_cap :
∀ {V X : Type} [inst : Fintype.{0} V] [DecidableEq.{1} V] (R : V → V → Prop)
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R) (ell : V → V → Bool) (P : X → Prop)
  (children : V → Bool → X) (C G : Finset.{0} V)
  (hdis : @Disjoint.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V) (@Finset.instOrderBot.{0} V) C G) (q a : Nat)
  (hexcl : @Sensitivity213981Formal.CandidateCoherence.NoOrdinary V R ell q a) (base : V → Bool)
  (hpartner :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) C w →
        ∀ (b : Bool), @Ne.{1} Bool b (base w) → P (children w b))
  (hhigh :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) G w →
        ∀ (b : Bool), P (children w b))
  (hC :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) C v →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} V (@Sensitivity213981Formal.TournamentHighRows.guardFailures V X inst R ell P children v))
          q)
  (hG :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) G v →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} V (@Sensitivity213981Formal.TournamentHighRows.guardFailures V X inst R ell P children v))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{0} V C) (@Finset.card.{0} V G)) a := by sorry
