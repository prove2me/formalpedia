-- Prove2me | Theorems.Thm_ThreeSum_Reporting_frontier_length_le_mass
-- name    : ThreeSum.Reporting.frontier_length_le_mass
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:02:40.203903+00:00
-- url     : https://prove2.me/theorems/4b9aad20-c3a9-4332-9dc6-901785997b87
-- title:
--   A positive reporting frontier is bounded by total incidence mass
-- statement:
--   Let $I$ be a finite set of incidences, each carrying a length-$J$ word $w_i$ over an alphabet with decidable equality and a natural weight $a_i$. Let the child list at each depth contain every symbol appearing there in these words, and assume every child list has no repetitions. Suppose the query returns the exact prefix mass at every depth $j\le J$:
--   $$
--   Q(j,u)=\sum_{\substack{i\in I\\\operatorname{take}_j(w_i)=u}}a_i.
--   $$
--   Starting with the empty prefix when its query is positive, form each frontier by appending the supplied children and retaining only positive-query prefixes. For every $k\le J$,
--   $$
--   |\operatorname{frontier}_k|\le\sum_{i\in I}a_i.
--   $$
--   This bounds the number of visited prefixes even when distinct incidences have identical words.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Reporting.lean#L126-L152

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Reporting_frontier_nodup
import Theorems.Thm_ThreeSum_Reporting_mem_frontier_iff


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2

theorem ThreeSum.Reporting.frontier_length_le_mass : ∀ {ι : Type u_1} {α : Type u_2} [inst : DecidableEq.{u_2 + 1} α] (I : Finset.{u_1} ι) (word : ι → List.{u_2} α)
  (weight : ι → Nat) (children : Nat → List.{u_2} α) (query : Nat → List.{u_2} α → Nat) (J k : Nat)
  (hlen :
    ∀ (i : ι),
      @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) I i →
        @Eq.{1} Nat (@List.length.{u_2} α (word i)) J)
  (hchildren :
    ∀ (i : ι)
      (hi :
        @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) I i)
      (j : Nat) (hj : @LT.lt.{0} Nat instLTNat j J),
      @Membership.mem.{u_2, u_2} α (List.{u_2} α) (@List.instMembership.{u_2} α) (children j)
        (@GetElem.getElem.{u_2, 0, u_2} (List.{u_2} α) Nat α
          (fun (as : List.{u_2} α) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{u_2} α as))
          (@List.instGetElemNatLtLength.{u_2} α) (word i) j
          (@Eq.mpr.{0} (@LT.lt.{0} Nat instLTNat j (@List.length.{u_2} α (word i))) (@LT.lt.{0} Nat instLTNat j J)
            (@id.{0}
              (@Eq.{1} Prop (@LT.lt.{0} Nat instLTNat j (@List.length.{u_2} α (word i))) (@LT.lt.{0} Nat instLTNat j J))
              (@congrArg.{1, 1} Nat Prop (@List.length.{u_2} α (word i)) J
                (fun (_a : Nat) => @LT.lt.{0} Nat instLTNat j _a) (hlen i hi)))
            hj)))
  (hquery :
    ∀ (j : Nat),
      @LE.le.{0} Nat instLENat j J →
        ∀ (pre : List.{u_2} α),
          @Eq.{1} Nat (query j pre) (@ThreeSum.Reporting.mass.{u_1, u_2} ι α inst I word weight j pre))
  (hc : ∀ (k : Nat), @List.Nodup.{u_2} α (children k)) (hk : @LE.le.{0} Nat instLENat k J),
  @LE.le.{0} Nat instLENat (@List.length.{u_2} (List.{u_2} α) (@ThreeSum.Reporting.frontier.{u_2} α children query k))
    (∑ i ∈ I, weight i) := by
  sorry
