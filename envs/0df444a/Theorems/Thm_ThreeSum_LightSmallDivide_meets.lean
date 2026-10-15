-- Prove2me | Theorems.Thm_ThreeSum_LightSmallDivide_meets
-- name    : ThreeSum.LightSmallDivide.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:35:50.332548+00:00
-- url     : https://prove2.me/theorems/c6b761e2-b9c1-4241-acf8-4112d59e3fd9
-- title:
--   Correctness of the small natural-division procedure
-- statement:
--   Fix a program containing the small-division procedure, resource limits, a call depth, and initial memory $\mu$. Let $a,b\in\mathbb N$ and suppose $a+b+2$ fits within the word-magnitude limit. With natural division's convention $a\mathbin{/}0=0$, the procedure called on $(a,b)$ returns
--
--   $$r=a\mathbin{/}b,\qquad\mu'=\mu,\qquad\text{cost}\le20(a\mathbin{/}b+1)+20.$$
--
--   This verifies the counting-loop division helper, including the zero-divisor branch, with time explicitly proportional to the quotient.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSmallDivide.lean#L26-L76

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
import Theorems.Thm_Light_Ends_of_blockSafe
import Theorems.Thm_Light_Ends_while


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightSmallDivide.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d p a b : Nat}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSmallDivide.body))
  (μ : Nat → Int)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      lim.word),
  Light.Meets lim P p d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b) (@List.nil.{0} Int)))
    μ (ThreeSum.LightSmallDivide.time a b) fun (r : Int) (μ' : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) a b)))
      (@Eq.{1} (Nat → Int) μ' μ) := by
  sorry
