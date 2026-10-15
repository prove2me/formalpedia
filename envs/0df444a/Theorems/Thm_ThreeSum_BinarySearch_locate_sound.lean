-- Prove2me | Theorems.Thm_ThreeSum_BinarySearch_locate_sound
-- name    : ThreeSum.BinarySearch.locate_sound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:41:25.421905+00:00
-- url     : https://prove2.me/theorems/13ef7987-f74b-4c6b-9bee-9ed4ed588df3
-- title:
--   Every returned interval contains the query
-- statement:
--   Let $\ell,h:\mathbb N\to\mathbb Z$, let $n\in\mathbb N$, and assume $\ell$ is nondecreasing on indices below $n$. For an integer query $x$, if the binary-search interval locator returns index $i$, then
--
--   $$
--   \operatorname{locate}(\ell,h,n,x)=\operatorname{some}(i)
--   \quad\Longrightarrow\quad i<n\ \land\ \ell(i)\le x\le h(i).
--   $$
--
--   No separation assumption on the intervals is needed for this soundness result. It certifies every successful band lookup even before uniqueness or completeness is used.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BinarySearch.lean#L111-L127

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Log
import Theorems.Thm_ThreeSum_BinarySearch_upperSearch_correct


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.BinarySearch.locate_sound : ∀ (lo hi : Nat → Int) (n : Nat) (x : Int)
  (hsorted :
    ∀ (i j : Nat),
      @LE.le.{0} Nat instLENat i j → @LT.lt.{0} Nat instLTNat j n → @LE.le.{0} Int Int.instLEInt (lo i) (lo j))
  {i : Nat} (h : @Eq.{1} (Option.{0} Nat) (ThreeSum.BinarySearch.locate lo hi n x) (@Option.some.{0} Nat i)),
  And (@LT.lt.{0} Nat instLTNat i n)
    (And (@LE.le.{0} Int Int.instLEInt (lo i) x) (@LE.le.{0} Int Int.instLEInt x (hi i))) := by
  sorry
