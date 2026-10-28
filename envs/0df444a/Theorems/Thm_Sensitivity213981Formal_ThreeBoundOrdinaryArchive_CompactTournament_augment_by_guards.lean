-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_CompactTournament_augment_by_guards
-- name    : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.CompactTournament.augment_by_guards
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:37:48.413842+00:00
-- url     : https://prove2.me/theorems/b51d2fda-28ee-4aed-8634-a2f60999b8d2
-- title:
--   Adding guard vertices loses at most one vertex
-- statement:
--   Let \(R\) be a relation on a finite vertex type such that every two distinct vertices are related in at least one direction. Let the directed edges carry binary labels \(\ell\), and let \(C,G\) be disjoint finite vertex sets. Write \(\delta_C(i)\) for the number of outgoing label mismatches from \(i\) into \(C\) under a prescribed coloring, and \(d_G^+(i)\) for the number of outgoing neighbors in \(G\). If
--   \[
--   \delta_C(i)+d_G^+(i)\le q\quad(i\in C),\qquad
--   \delta_C(i)+d_G^+(i)\le q+1\quad(i\in G),
--   \]
--   then there is a colored set \(S\) satisfying
--   \[
--   |S|\ge |C|+|G|-1
--   \]
--   whose every vertex has at most \(q\) outgoing mismatches inside \(S\). This converts a mixed target-and-guard set into an ordinary coherent-set obstruction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ArchivedOrdinaryCaps.lean, lines 481–557.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_ArchivedOrdinaryDefinitions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundOrdinaryArchive.CompactTournament.augment_by_guards.{u_1} :
∀ {V : Type u_1} [Fintype.{u_1} V] [DecidableEq.{u_1 + 1} V] (R : V → V → Prop)
  (ht : ∀ (x y : V), @Ne.{u_1 + 1} V x y → Or (R x y) (R y x))
  (ell : Prod.{u_1, u_1} V V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (C G : Finset.{u_1} V)
  (hdis : @Disjoint.{u_1} (Finset.{u_1} V) (@Finset.instPartialOrder.{u_1} V) (@Finset.instOrderBot.{u_1} V) C G)
  (q : Nat) (base : V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hC :
    ∀ (i : V),
      @Membership.mem.{u_1, u_1} V (Finset.{u_1} V)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} V) V (@Finset.instSetLike.{u_1} V)) C i →
        @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Finset.card.{u_1} V
              (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.mismatch.{u_1} V R ell C base i))
            (@Finset.card.{u_1} V (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.outOn.{u_1} V R G i)))
          q)
  (hG :
    ∀ (i : V),
      @Membership.mem.{u_1, u_1} V (Finset.{u_1} V)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} V) V (@Finset.instSetLike.{u_1} V)) G i →
        @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Finset.card.{u_1} V
              (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.mismatch.{u_1} V R ell C base i))
            (@Finset.card.{u_1} V (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.outOn.{u_1} V R G i)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  @Exists.{u_1 + 1} (Finset.{u_1} V) fun (S : Finset.{u_1} V) =>
    @Exists.{u_1 + 1} (V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      fun (color : V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
      And
        (@LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{u_1} V C)
            (@Finset.card.{u_1} V G))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{u_1} V S)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.OrdinaryGood.{u_1} V R ell S q color) := by sorry
