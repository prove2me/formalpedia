-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ResidualCaps_actual_dominator_residual_cap
-- name    : Sensitivity213981Formal.ResidualCaps.actual_dominator_residual_cap
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:37:45.457996+00:00
-- url     : https://prove2.me/theorems/7dffc97d-6b80-4652-8345-07a86713238a
-- title:
--   Deleting marker mismatches yields a residual dominator bound
-- statement:
--   Let A be a set of zero-failure candidates in a labelled tournament, disjoint from a set H of high vertices whose two guard children accept. Choose m markers M⊆H and a color for each candidate, with the opposite child accepting at the guard level. If every coherent set dominated by m markers has cardinality less than a, then |A|≤a−1+∑_{v∈M} residual(v), where residual(v) counts the guard failures of marker v outside H.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ResidualCaps.lean, lines 118–150.

import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
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

theorem Sensitivity213981Formal.ResidualCaps.actual_dominator_residual_cap :
∀ {V X : Type} [inst : Fintype.{0} V] [inst_1 : DecidableEq.{1} V] (R : V → V → Prop)
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R) (ell : V → V → Bool) (guard : X → Prop)
  (children : V → Bool → X) (A H M : Finset.{0} V)
  (hdis : @Disjoint.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V) (@Finset.instOrderBot.{0} V) A H)
  (hMH :
    @LE.le.{0} (Finset.{0} V)
      (@Preorder.toLE.{0} (Finset.{0} V) (@PartialOrder.toPreorder.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V)))
      M H)
  (color : V → Bool) (m a : Nat) (hM : @Eq.{1} Nat (@Finset.card.{0} V M) m)
  (hcap : @Sensitivity213981Formal.ResidualCaps.DominatorCardBound V inst_1 R ell m a)
  (hpartner :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) A w →
        ∀ (c : Bool), @Ne.{1} Bool c (color w) → guard (children w c))
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
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))),
  @LE.le.{0} Nat instLENat (@Finset.card.{0} V A)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid M fun (v : V) =>
        @Sensitivity213981Formal.ResidualCaps.residual V X inst R ell guard children H v)) := by sorry
