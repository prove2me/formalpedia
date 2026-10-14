-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_small_lift_exists
-- name    : ThreeSum.Arithmetic.small_lift_exists
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:32:57.894473+00:00
-- url     : https://prove2.me/theorems/633f6586-bf30-4344-b8b4-134c5324bf83
-- title:
--   A modular triple has a small signed lift
-- statement:
--   Let $P,a,b,c\in\mathbb Z$ satisfy $P>0$ and $0\le a,b,c<P$. Assume $P\mid(c-b-a)$, so these canonical residues satisfy the required modular relation. Then
--
--   $$\exists j\in\{-1,0,1\}:\qquad c-b=a+jP.$$
--
--   Thus the fixed three-element signed-lift list covers every modular candidate formed from canonical residues. The statement supplies the completeness direction needed when modular relations are represented by a short list of integer equations.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Arithmetic.lean#L117-L139

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

theorem ThreeSum.Arithmetic.small_lift_exists : ∀ {P a b c : Int} (hP : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) P)
  (ha0 : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) a)
  (haP : @LT.lt.{0} Int Int.instLTInt a P)
  (hb0 : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) b)
  (hbP : @LT.lt.{0} Int Int.instLTInt b P)
  (hc0 : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) c)
  (hcP : @LT.lt.{0} Int Int.instLTInt c P)
  (hdiv :
    @Dvd.dvd.{0} Int Int.instDvd P
      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) c b) a)),
  ∃ (j : Int),
    And (ThreeSum.Arithmetic.SmallLift j)
      (@Eq.{1} Int (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) c b)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) a
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) j P))) := by
  sorry
