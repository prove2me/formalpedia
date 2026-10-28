-- Prove2me | Theorems.Thm_Sensitivity213981Formal_GuardAugmentation_augment_by_guards
-- name    : Sensitivity213981Formal.GuardAugmentation.augment_by_guards
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:31:19.767395+00:00
-- url     : https://prove2.me/theorems/f96066db-e745-40c9-ad40-203667a5ca82
-- title:
--   Boolean guard augmentation preserves all but one candidate
-- statement:
--   Let \(C,G\) be disjoint finite sets in a relation that orients at least one direction between distinct vertices, with Boolean edge labels and a prescribed coloring on \(C\). Suppose the sum of mismatches into \(C\) and outgoing neighbors in \(G\) is at most \(q\) for vertices of \(C\), and at most \(q+1\) for vertices of \(G\). Then a colored set \(S\) exists with
--   \[
--   |S|\ge |C|+|G|-1,
--   \]
--   such that every vertex of \(S\) has at most \(q\) internal outgoing mismatches. This version uses the Boolean labels of the graded construction and requires no equality of target thresholds.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; GuardAugmentation.lean, lines 99–177.

import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_Namespaces
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

theorem Sensitivity213981Formal.GuardAugmentation.augment_by_guards :
∀ {V : Type} [Fintype.{0} V] [DecidableEq.{1} V] (R : V → V → Prop)
  (ht : ∀ (x y : V), @Ne.{1} V x y → Or (R x y) (R y x)) (ell : V → V → Bool) (C G : Finset.{0} V)
  (hdis : @Disjoint.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V) (@Finset.instOrderBot.{0} V) C G) (q : Nat)
  (base : V → Bool)
  (hC :
    ∀ (i : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) C i →
        @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Finset.card.{0} V (@Sensitivity213981Formal.CandidateCoherence.mismatch V R ell C base i))
            (@Finset.card.{0} V (@Sensitivity213981Formal.TournamentHighRows.outNeighbors V R G i)))
          q)
  (hG :
    ∀ (i : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) G i →
        @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Finset.card.{0} V (@Sensitivity213981Formal.CandidateCoherence.mismatch V R ell C base i))
            (@Finset.card.{0} V (@Sensitivity213981Formal.TournamentHighRows.outNeighbors V R G i)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  @Exists.{1} (Finset.{0} V) fun (S : Finset.{0} V) =>
    @Exists.{1} (V → Bool) fun (color : V → Bool) =>
      And
        (@LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{0} V C)
            (@Finset.card.{0} V G))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{0} V S)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Sensitivity213981Formal.CandidateCoherence.OrdinaryGood V R ell S q color) := by sorry
