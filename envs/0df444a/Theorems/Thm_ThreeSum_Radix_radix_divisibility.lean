-- Prove2me | Theorems.Thm_ThreeSum_Radix_radix_divisibility
-- name    : ThreeSum.Radix.radix_divisibility
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:28:59.494374+00:00
-- url     : https://prove2.me/theorems/e32cee6c-9485-4fc9-83c8-d63bbb8516ee
-- title:
--   Divisibility splits into a radix digit and its quotient target
-- statement:
--   Let $p,a,h,t\in\mathbb Z$ with $p\ne0$, and let $j\in\mathbb N$. Divisibility through one positional digit satisfies
--
--   $$
--   p^{j+1}\mid a-(h+pt)
--   \quad\Longleftrightarrow\quad
--   p\mid a-h\ \text{ and }\ p^j\mid\frac{a-h}{p}-t.
--   $$
--
--   The quotient is integer division; on the right, the first divisibility condition makes it exact. The radix may be negative, and the statement includes $j=0$.
--
--   This algebraic equivalence underlies the recursive radix representation rule, determining the next quotient target from the current digit without introducing an independent carry choice.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Radix.lean#L42-L64

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.Radix.radix_divisibility : ∀ (p a h t : Int) (hp : @Ne.{1} Int p (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (j : Nat),
  Iff
    (@Dvd.dvd.{0} Int Int.instDvd
      (@HPow.hPow.{0, 0, 0} Int Nat Int
        (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) p
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) a
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) h
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) p t))))
    (And (@Dvd.dvd.{0} Int Int.instDvd p (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) a h))
      (@Dvd.dvd.{0} Int Int.instDvd
        (@HPow.hPow.{0, 0, 0} Int Nat Int
          (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) p j)
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
          (@HDiv.hDiv.{0, 0, 0} Int Int Int (@instHDiv.{0} Int Int.instDiv)
            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) a h) p)
          t))) := by
  sorry
