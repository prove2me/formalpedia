-- Prove2me | Theorems.Thm_ThreeSum_LightSourceControlsMax_meets
-- name    : ThreeSum.LightSourceControlsMax.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:28:20.784005+00:00
-- url     : https://prove2.me/theorems/a13ce159-852d-4100-8c12-d3185cc80351
-- title:
--   A fixed machine procedure computes a scalar maximum
-- statement:
--   Let $a,b\in\mathbb N$ and let a program contain the fixed two-argument maximum procedure at index $p$. If its word-magnitude limit is at least $\max(a,b)$, then for every initial integer memory $\mu$ and every call depth $d$, the procedure satisfies
--
--   $$
--   P_p(a,b;\mu)\text{ returns }\max(a,b)
--   \text{ within }40\text{ steps, with final memory }\mu.
--   $$
--
--   The two inputs may be zero or equal. There is no memory-space assumption because this procedure only compares and assigns local variables.
--
--   The contract supplies the scalar maximum operation used to combine independently computed shared-bank dimensions.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceControlsMax.lean#L13-L26

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightSourceControlsMax.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d p a b : Nat}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSourceControlsMax.body))
  (μ : Nat → Int)
  (hword : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (@Max.max.{0} Nat Nat.instMax a b)) lim.word),
  Light.Meets lim P p d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b) (@List.nil.{0} Int)))
    μ (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) fun (r : Int) (ν : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (@Max.max.{0} Nat Nat.instMax a b))) (@Eq.{1} (Nat → Int) ν μ) := by
  sorry
