-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundPrefixCaps_ordinary_prefix_cap
-- name    : Sensitivity213981Formal.ThreeBoundPrefixCaps.ordinary_prefix_cap
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:45:00.014999+00:00
-- url     : https://prove2.me/theorems/8f58f036-a7f6-46ed-a6e1-131cacc854d6
-- title:
--   Ordinary exclusion bounds a target prefix after high-head augmentation
-- statement:
--   Let T be a candidate set whose selected complementary children satisfy a guard predicate, with each candidate having at most q guard failures. Let H be a set whose two children satisfy that predicate. If there is no ordinary coherent q-defect set of size a, then |T| is at most the minimum of a−1−h_q and a−h_{q+1}, where h_b counts vertices of H outside T having at most b guard failures. Subtraction is natural-number subtraction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ActualPrefixCaps.lean, lines 24–49.

import Definitions.Def_Sensitivity213981Formal_ActualPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundPrefixCaps.ordinary_prefix_cap :
∀ {V X : Type} [inst : Fintype.{0} V] [inst_1 : DecidableEq.{1} V] (R : V → V → Prop)
  (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R) (ell : V → V → Bool) (P : X → Prop)
  (children : V → Bool → X) (T H : Finset.{0} V) (color : V → Bool) (q a : Nat)
  (hexcl : @Sensitivity213981Formal.CandidateCoherence.NoOrdinary V R ell q a)
  (hpartner :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) T w →
        ∀ (c : Bool), @Ne.{1} Bool c (color w) → P (children w c))
  (hhigh :
    ∀ (w : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) H w →
        ∀ (c : Bool), P (children w c))
  (hT :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) T v →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} V (@Sensitivity213981Formal.TournamentHighRows.guardFailures V X inst R ell P children v))
          q),
  @LE.le.{0} Nat instLENat (@Finset.card.{0} V T)
    (@Min.min.{0} Nat instMinNat
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Finset.card.{0} V
          (@Sensitivity213981Formal.ThreeBoundPrefixCaps.outsideHigh V X inst inst_1 R ell P children H T q)))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
        (@Finset.card.{0} V
          (@Sensitivity213981Formal.ThreeBoundPrefixCaps.outsideHigh V X inst inst_1 R ell P children H T
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) := by sorry
