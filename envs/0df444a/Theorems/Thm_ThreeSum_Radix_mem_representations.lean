-- Prove2me | Theorems.Thm_ThreeSum_Radix_mem_representations
-- name    : ThreeSum.Radix.mem_representations
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:01:29.190192+00:00
-- url     : https://prove2.me/theorems/508a81fc-52f2-430c-93b8-1936b3341fae
-- title:
--   Exact membership in the recursive radix representation family
-- statement:
--   Let $\Omega$ be a finite type with decidable equality, let $p\in\mathbb Z\setminus\{0\}$, and let $\ell,r:\Omega\to\mathbb Z$ be endpoint maps. For a list $x=(x_0,\ldots,x_{s-1})$, define the low-digit-first positional hash $H_u(x)=\sum_{i<s}p^i u(x_i)$.
--
--   The recursive family $R_j(a,b)$ chooses a first symbol whose two endpoint differences are divisible by $p$, then recurses on the quotient targets; $R_0(a,b)=\{[]\}$. For all natural $j$, integer targets $a,b$, and lists $x$,
--   $$
--   x\in R_j(a,b)\iff |x|=j\ \land\ p^j\mid a-H_\ell(x)\ \land\ p^j\mid b-H_r(x).
--   $$
--   This identifies the recursive candidate family with exactly the simultaneous positional congruences, including the original local choices.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Radix.lean#L66-L87

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Radix_radix_divisibility


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.Radix.mem_representations : ∀ {Ω : Type u_1} [inst : Fintype.{u_1} Ω] [inst_1 : DecidableEq.{u_1 + 1} Ω] (p : Int)
  (hp : @Ne.{1} Int p (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (left right : Ω → Int) (j : Nat)
  (a b : Int) (xs : List.{u_1} Ω),
  Iff
    (@Membership.mem.{u_1, u_1} (List.{u_1} Ω) (Finset.{u_1} (List.{u_1} Ω))
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (List.{u_1} Ω)) (List.{u_1} Ω)
        (@Finset.instSetLike.{u_1} (List.{u_1} Ω)))
      (@ThreeSum.Radix.representations.{u_1} Ω inst inst_1 p left right j a b) xs)
    (And (@Eq.{1} Nat (@List.length.{u_1} Ω xs) j)
      (And
        (@Dvd.dvd.{0} Int Int.instDvd
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) p j)
          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) a
            (@ThreeSum.Radix.positionalHash.{u_1} Ω p left xs)))
        (@Dvd.dvd.{0} Int Int.instDvd
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) p j)
          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) b
            (@ThreeSum.Radix.positionalHash.{u_1} Ω p right xs))))) := by
  sorry
