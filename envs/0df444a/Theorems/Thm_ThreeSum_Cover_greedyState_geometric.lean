-- Prove2me | Theorems.Thm_ThreeSum_Cover_greedyState_geometric
-- name    : ThreeSum.Cover.greedyState_geometric
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:39:07.138335+00:00
-- url     : https://prove2.me/theorems/0e9671a5-2e0e-4e49-afab-647e0840e241
-- title:
--   Geometric decay of the greedy uncovered set
-- statement:
--   Let $\Omega$ be a finite nonempty collection of maps, supplied as a list containing every map, and let $T$ be a finite target set in a type with decidable equality. Let the covering relation be decidable. Suppose $a\in\mathbb N$ is positive and every $u\in T$ is covered by at least a $1/a$ fraction of $\Omega$, in the integer form $|\Omega|\le a|\{\omega:\omega\text{ covers }u\}|$. Let $G_t$ be the targets left after $t$ greedy steps, each selecting a map covering the most remaining targets. Then
--
--   $$
--   a^t|G_t|\le(a-1)^t|T|\qquad(t\in\mathbb N).
--   $$
--
--   This denominator-free estimate turns a uniform coverage frequency into a bound on the deterministic greedy schedule length.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Greedy.lean#L97-L115

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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2

theorem ThreeSum.Cover.greedyState_geometric : ∀ {Ω : Type u_1} {U : Type u_2} [inst : Inhabited.{u_1 + 1} Ω] [DecidableEq.{u_2 + 1} U] [inst_2 : Fintype.{u_1} Ω]
  (maps : List.{u_1} Ω)
  (hall : ∀ (ω : Ω), @Membership.mem.{u_1, u_1} Ω (List.{u_1} Ω) (@List.instMembership.{u_1} Ω) maps ω)
  (covers : Ω → U → Prop) [inst_3 : @DecidableRel.{u_1 + 1, u_2 + 1} Ω U covers] (targets : Finset.{u_2} U) (a : Nat)
  (ha : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a)
  (hfrequency :
    ∀ (u : U),
      @Membership.mem.{u_2, u_2} U (Finset.{u_2} U)
          (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} U) U (@Finset.instSetLike.{u_2} U)) targets u →
        @LE.le.{0} Nat instLENat (@Fintype.card.{u_1} Ω inst_2)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a
            (@Finset.card.{u_1} Ω {ω : Ω | covers ω u})))
  (t : Nat),
  @LE.le.{0} Nat instLENat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) a t)
      (@Finset.card.{u_2} U (@ThreeSum.Cover.greedyState.{u_1, u_2} Ω U inst maps covers inst_3 targets t)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        t)
      (@Finset.card.{u_2} U targets)) := by
  sorry
