-- Prove2me | Theorems.Thm_ThreeSum_LightTrimTest_meets
-- name    : ThreeSum.LightTrimTest.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:44:43.201581+00:00
-- url     : https://prove2.me/theorems/95c8971a-fd82-4f91-bab8-9726700e5867
-- title:
--   Correctness of the constant-time retained-edge test
-- statement:
--   Let $x,\ell,r,b\in\mathbb N$, let $\mu:\mathbb N\to\mathbb Z$ be memory, and suppose procedure $p$ in a program $P$ is the specified trimming-test body. Under machine limits whose word bound $W$ satisfies $1\le W$ and $b+1\le W$, the procedure at any call depth, on arguments $(x,\ell,r,b)$, terminates within $30$ steps with
--
--   $$
--   v=\begin{cases}1&x=0\ \land\ \ell\le b\ \land\ r\le b,\\0&\text{otherwise},\end{cases}
--   \qquad \mu'=\mu.
--   $$
--
--   This verifies the actual local retained-edge decision and its unchanged-memory contract.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightTrimTest.lean#L32-L54

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
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

theorem ThreeSum.LightTrimTest.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d p x l r b : Nat}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt ThreeSum.LightTrimTest.body))
  (μ : Nat → Int)
  (hword : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) lim.word)
  (hcap :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      lim.word),
  Light.Meets lim P p d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt x)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt l)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt r)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b) (@List.nil.{0} Int)))))
    μ ThreeSum.LightTrimTest.time fun (v : Int) (μ' : Nat → Int) =>
    And (@Eq.{1} Int v (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightTrimTest.flag x l r b)))
      (@Eq.{1} (Nat → Int) μ' μ) := by
  sorry
