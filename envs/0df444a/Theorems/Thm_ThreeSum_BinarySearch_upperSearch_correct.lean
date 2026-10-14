-- Prove2me | Theorems.Thm_ThreeSum_BinarySearch_upperSearch_correct
-- name    : ThreeSum.BinarySearch.upperSearch_correct
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:36:18.676745+00:00
-- url     : https://prove2.me/theorems/dcb60f13-8ca0-40b7-a933-193bdf70112d
-- title:
--   Correctness of the upper-bound binary search
-- statement:
--   Let $f:\mathbb N\to\mathbb Z$ be nondecreasing on its first $n$ entries, and let $x\in\mathbb Z$. Choose natural numbers $b,\ell,h$ with $\ell\le h\le n$ and $h-\ell<2^b$. Assume every index below $\ell$ has value at most $x$, and every index from $h$ to $n-1$ has value strictly above $x$. If $k$ is the result of the upper-bound search with fuel $b$ and interval $[\ell,h)$, then
--
--   $$
--   k\le n,\qquad (\forall i<k,\ f(i)\le x),\qquad (\forall k\le i<n,\ x<f(i)).
--   $$
--
--   Thus the bounded search returns the correct partition point, including when the result is the end of the array.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BinarySearch.lean#L51-L87

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Log


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.BinarySearch.upperSearch_correct : ∀ (f : Nat → Int) (x : Int) (n fuel lo hi : Nat)
  (hsorted :
    ∀ (i j : Nat),
      @LE.le.{0} Nat instLENat i j → @LT.lt.{0} Nat instLTNat j n → @LE.le.{0} Int Int.instLEInt (f i) (f j))
  (hlo : @LE.le.{0} Nat instLENat lo hi) (hhi : @LE.le.{0} Nat instLENat hi n)
  (hwidth :
    @LT.lt.{0} Nat instLTNat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) hi lo)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) fuel))
  (hlower : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i lo → @LE.le.{0} Int Int.instLEInt (f i) x)
  (hupper :
    ∀ (i : Nat), @LE.le.{0} Nat instLENat hi i → @LT.lt.{0} Nat instLTNat i n → @LT.lt.{0} Int Int.instLTInt x (f i)),
  ThreeSum.BinarySearch.Partition f x n (ThreeSum.BinarySearch.upperSearch f x fuel lo hi) := by
  sorry
