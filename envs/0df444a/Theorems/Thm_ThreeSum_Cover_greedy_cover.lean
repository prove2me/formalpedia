-- Prove2me | Theorems.Thm_ThreeSum_Cover_greedy_cover
-- name    : ThreeSum.Cover.greedy_cover
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:44:10.387269+00:00
-- url     : https://prove2.me/theorems/7e54ed46-7334-4fb6-b6f2-9e265e4f9309
-- title:
--   The concrete greedy procedure covers every target in logarithmically many rounds
-- statement:
--   Let $\Omega$ be a nonempty finite set of maps, supplied by a list containing every element, and let $T$ be a finite target set. Assume coverage is decidable. For an integer $a>1$, suppose each target is covered by at least a $1/a$ fraction of all maps:
--
--   $$|\Omega|\le a\,|\{\omega\in\Omega:\omega\text{ covers }u\}|\qquad(u\in T).$$
--
--   Let $G_m$ be the implemented greedy choice list, selecting a map with maximum remaining coverage and breaking ties by the supplied order. For $m=a(\log_2^{\mathrm{nat}}|T|+1)$,
--
--   $$\forall u\in T,\quad\exists\omega\in G_m:\omega\text{ covers }u.$$
--
--   This proves a finite cover bound for the actual executable selection rule, allowing repeated maps in the input or output lists.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Greedy.lean#L144-L165

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.MinMax
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Cover_greedyState_geometric


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2

theorem ThreeSum.Cover.greedy_cover : ∀ {Ω : Type u_1} {U : Type u_2} [inst : Inhabited.{u_1 + 1} Ω] [DecidableEq.{u_2 + 1} U] [inst_2 : Fintype.{u_1} Ω]
  (maps : List.{u_1} Ω)
  (hall : ∀ (ω : Ω), @Membership.mem.{u_1, u_1} Ω (List.{u_1} Ω) (@List.instMembership.{u_1} Ω) maps ω)
  (covers : Ω → U → Prop) [inst_3 : @DecidableRel.{u_1 + 1, u_2 + 1} Ω U covers] (targets : Finset.{u_2} U) (a : Nat)
  (ha : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a)
  (hfrequency :
    ∀ (u : U),
      @Membership.mem.{u_2, u_2} U (Finset.{u_2} U)
          (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} U) U (@Finset.instSetLike.{u_2} U)) targets u →
        @LE.le.{0} Nat instLENat (@Fintype.card.{u_1} Ω inst_2)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a
            (@Finset.card.{u_1} Ω {ω : Ω | covers ω u})))
  (u : U),
  @Membership.mem.{u_2, u_2} U (Finset.{u_2} U)
      (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} U) U (@Finset.instSetLike.{u_2} U)) targets u →
    ∃ (ω : Ω),
      And
        (@Membership.mem.{u_1, u_1} Ω (List.{u_1} Ω) (@List.instMembership.{u_1} Ω)
          (@ThreeSum.Cover.greedyChoices.{u_1, u_2} Ω U inst maps covers inst_3 targets
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{u_2} U targets).log2
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          ω)
        (covers ω u) := by
  sorry
