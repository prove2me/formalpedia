-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_early_yes
-- name    : ThreeSum.Arithmetic.early_yes
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:33:14.825983+00:00
-- url     : https://prove2.me/theorems/640c7715-1d87-4e7e-bd2f-d316793ea652
-- title:
--   Excess incidence mass forces a good owner
-- statement:
--   Let $I$ be a finite set of incidences, $\tau$ a finite owner set, $o:I\to\tau$ the owner map, and $w_i\in\mathbb N$ the incidence weights. Let $G\subseteq\tau$ be the good owners, and let $R,H\in\mathbb N$. Suppose each bad owner has fiber weight at most $R$, and there are at most $H$ bad owners:
--
--   $$\sum_{i\in I:\,o(i)=t}w_i\le R\quad(t\notin G),\qquad |\tau\setminus G|\le H.$$
--
--   If $\sum_{i\in I}w_i>RH$, then
--
--   $$\exists i\in I:\quad w_i>0\ \land\ o(i)\in G.$$
--
--   This counting criterion justifies an early positive answer when represented mass exceeds the maximum mass attributable to false original candidates.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Arithmetic.lean#L301-L351

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2

theorem ThreeSum.Arithmetic.early_yes : ∀ {ι : Type u_1} {τ : Type u_2} [inst : Fintype.{u_2} τ] [inst_1 : DecidableEq.{u_2 + 1} τ] (I : Finset.{u_1} ι)
  (owner : ι → τ) (weight : ι → Nat) (good : τ → Prop) [inst_2 : @DecidablePred.{u_2 + 1} τ good] (Rmax H : Nat)
  (hcap :
    ∀ (t : τ),
      Not (good t) →
        @LE.le.{0} Nat instLENat (@ThreeSum.Arithmetic.fiberWeight.{u_1, u_2} ι τ inst_1 I owner weight t) Rmax)
  (hcount : @LE.le.{0} Nat instLENat (@Finset.card.{u_2} τ {t : τ | Not (good t)}) H)
  (hlarge :
    @LT.lt.{0} Nat instLTNat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Rmax H)
      (∑ i ∈ I, weight i)),
  ∃ (i : ι),
    And
      (@Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) I i)
      (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (weight i))
        (good (owner i))) := by
  sorry
