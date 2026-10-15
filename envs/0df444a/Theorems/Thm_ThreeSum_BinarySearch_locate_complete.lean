-- Prove2me | Theorems.Thm_ThreeSum_BinarySearch_locate_complete
-- name    : ThreeSum.BinarySearch.locate_complete
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:41:16.817242+00:00
-- url     : https://prove2.me/theorems/083bea9d-b0dc-488b-947f-a90a2c53ebb0
-- title:
--   Interval lookup finds every containing separated interval
-- statement:
--   Let $\ell,h:\mathbb N\to\mathbb Z$ describe $n$ closed intervals. Suppose their lower endpoints are nondecreasing, and whenever $i<j<n$ the strict separation $h(i)<\ell(j)$ holds. If $i<n$ and $\ell(i)\le x\le h(i)$, then the binary-search interval locator returns
--
--   $$
--   \operatorname{locate}(\ell,h,n,x)=\operatorname{some}(i).
--   $$
--
--   The locator first finds the upper-bound position among the lower endpoints and then checks the preceding interval's upper endpoint. This establishes completeness of the interval access used to identify a matching band.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BinarySearch.lean#L129-L146

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Log
import Theorems.Thm_ThreeSum_BinarySearch_upperSearch_correct


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.BinarySearch.locate_complete : ∀ (lo hi : Nat → Int) (n : Nat) (x : Int)
  (hsorted :
    ∀ (i j : Nat),
      @LE.le.{0} Nat instLENat i j → @LT.lt.{0} Nat instLTNat j n → @LE.le.{0} Int Int.instLEInt (lo i) (lo j))
  (hseparated :
    ∀ (i j : Nat),
      @LT.lt.{0} Nat instLTNat i j → @LT.lt.{0} Nat instLTNat j n → @LT.lt.{0} Int Int.instLTInt (hi i) (lo j))
  {i : Nat} (hin : @LT.lt.{0} Nat instLTNat i n) (hil : @LE.le.{0} Int Int.instLEInt (lo i) x)
  (hih : @LE.le.{0} Int Int.instLEInt x (hi i)),
  @Eq.{1} (Option.{0} Nat) (ThreeSum.BinarySearch.locate lo hi n x) (@Option.some.{0} Nat i) := by
  sorry
