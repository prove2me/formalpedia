-- Prove2me | Theorems.Thm_Sensitivity213981Formal_CandidateCoherence_target_plus_high_cap
-- name    : Sensitivity213981Formal.CandidateCoherence.target_plus_high_cap
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:26:46.538893+00:00
-- url     : https://prove2.me/theorems/9c1b09e4-48ff-4c8e-9d3d-f1e7f588e5b9
-- title:
--   An ordinary exclusion bounds targets together with high vertices
-- statement:
--   Fix a directed relation \(R\), binary labels \(\ell\), a child predicate \(P\), and two children at every vertex. Let \(T,H\) be disjoint finite sets. Each vertex of \(T\) has a designated color whose other child satisfies \(P\); both children of every vertex of \(H\) satisfy \(P\). Assume each vertex in \(T\cup H\) has at most \(q\) failed guards. If no ordinarily coherent \(a\)-vertex configuration of tolerance \(q\) exists, then
--   \[
--   |T|+|H|<a.
--   \]
--   This strengthens a target-prefix cap by including high vertices at the same failure budget.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; CandidateCoherence.lean, lines 156–180.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_CandidateCoherence
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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

theorem Sensitivity213981Formal.CandidateCoherence.target_plus_high_cap :
∀ {V X : Type} [inst : Fintype.{0} V] (R : V → V → Prop) (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
  (T H : Finset.{0} V)
  (hdisjoint : @Disjoint.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V) (@Finset.instOrderBot.{0} V) T H)
  (q a : Nat) (hexcl : @Sensitivity213981Formal.CandidateCoherence.NoOrdinary V R ell q a) (color : V → Bool)
  (hpartner :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) T w →
        ∀ (b : Bool), @Ne.{1} Bool b (color w) → P (children w b))
  (hhigh :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H w →
        ∀ (b : Bool), P (children w b))
  (hbudgetT :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) T v →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} V (@Sensitivity213981Formal.TournamentHighRows.guardFailures V X inst R ell P children v))
          q)
  (hbudgetH :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H v →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} V (@Sensitivity213981Formal.TournamentHighRows.guardFailures V X inst R ell P children v))
          q),
  @LT.lt.{0} Nat instLTNat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{0} V T) (@Finset.card.{0} V H)) a := by sorry
