-- Prove2me | Theorems.Thm_ThreeSum_LightNatPower_meets
-- name    : ThreeSum.LightNatPower.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:04:54.302987+00:00
-- url     : https://prove2.me/theorems/d50c2e07-e87b-460c-8d01-d2898880184d
-- title:
--   Verified natural exponentiation by repeated multiplication
-- statement:
--   Let $b,e\in\mathbb N$, let $\mu$ be any memory, and suppose the Light program contains the natural-power body. Assume $e\le\mathrm{word}$ and $b^i\le\mathrm{word}$ for every $0\le i\le e$.
--
--   The call with arguments $(b,e)$ terminates within $20e+20$ steps and returns
--   $$
--   r=b^e,\qquad \nu=\mu.
--   $$
--   The conclusion includes exponent zero, for which the result is one. This certifies the scalar exponentiation routine used to compute finite layout and enumeration sizes.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightNatPower.lean#L24-L56

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_Ends_for


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightNatPower.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d p b e : Nat}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt ThreeSum.LightNatPower.body))
  (μ : Nat → Int) (he : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt e) lim.word)
  (hpow :
    ∀ (i : Nat),
      @LE.le.{0} Nat instLENat i e →
        @LE.le.{0} Int Int.instLEInt
          (@Nat.cast.{0} Int instNatCastInt
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) b i))
          lim.word),
  Light.Meets lim P p d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt e) (@List.nil.{0} Int)))
    μ (ThreeSum.LightNatPower.time e) fun (r : Int) (μ' : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) b e)))
      (@Eq.{1} (Nat → Int) μ' μ) := by
  sorry
