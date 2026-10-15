-- Prove2me | Theorems.Thm_ThreeSum_LightSourceFlagTest_meets
-- name    : ThreeSum.LightSourceFlagTest.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:28:26.475877+00:00
-- url     : https://prove2.me/theorems/08932b4b-491a-407e-a4d9-221d3fb9ca79
-- title:
--   The machine trimming flag tests cardinality and bucket size exactly
-- statement:
--   Let $c,r,n,b\in\mathbb N$ denote a measured cardinality, required cardinality, bucket count, and cap. Suppose procedure $p$ contains the fixed flag-test body and the machine word-magnitude limit is at least $c+r+n+b+2$. For any initial integer memory $\mu$ and call depth, it returns within $25$ steps with
--
--   $$
--   \mathrm{result}=\begin{cases}
--   1,&c=r\text{ and }n\le b,\\
--   0,&\text{otherwise},
--   \end{cases}
--   \qquad \mathrm{final\ memory}=\mu.
--   $$
--
--   All four parameters may be zero.
--
--   This contract implements the two independent retention conditions used in the source construction: the prescribed subset cardinality and a sufficiently small hash bucket.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceFlagTest.lean#L30-L47

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

theorem ThreeSum.LightSourceFlagTest.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d p card required count cap : Nat}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSourceFlagTest.body))
  (μ : Nat → Int)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) card required) count)
            cap)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      lim.word),
  Light.Meets lim P p d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt card)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt required)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt count)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cap) (@List.nil.{0} Int)))))
    μ ThreeSum.LightSourceFlagTest.time fun (r : Int) (ν : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceFlagTest.flag card required count cap)))
      (@Eq.{1} (Nat → Int) ν μ) := by
  sorry
