-- Prove2me | Theorems.Thm_ThreeSum_LightReportingBucketRow_meets
-- name    : ThreeSum.LightReportingBucketRow.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:04:52.109501+00:00
-- url     : https://prove2.me/theorems/a5785ce8-53b6-4d85-bece-bbd29d941c67
-- title:
--   Verified count of a target value along a bucket-index row
-- statement:
--   Let $v:\mathbb N\to\mathbb Z$ describe a length-$N$ value array at address $A$, and let $q:\mathbb N\to\mathbb N$ describe a length-$n$ index row at address $I$, with $q(i)<N$ for $i<n$. Let $a\in\mathbb Z$ be the target. Suppose both arrays fit within $\mathrm{space}\le\mathrm{word}$, memory contains the stated values and indices, and $|a|,|v(j)|\le\mathrm{word}$ for all $j<N$.
--
--   If the Light program contains the bucket-row body, its call with $(a,A,I,n,N)$ terminates within $60n+30$ steps and satisfies
--   $$
--   r=\bigl|\{i<n:v(q(i))=a\}\bigr|,\qquad \nu=\mu.
--   $$
--   This counts matching original values in the supplied physical index row, including repeated index occurrences.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingBucketRow.lean#L57-L102

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
import Definitions.Def_ThreeSum1962Source_Bundle02
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
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
import Theorems.Thm_Light_Ends_for


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightReportingBucketRow.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d p src indices n N : Nat} {μ : Nat → Int}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt ThreeSum.LightReportingBucketRow.body))
  (target : Int) (value : Nat → Int) (index : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src N) lim.space)
  (hindices :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) indices n) lim.space)
  (hindex : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i n → @LT.lt.{0} Nat instLTNat (index i) N)
  (hreadI :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) indices i))
          (@Nat.cast.{0} Int instNatCastInt (index i)))
  (hreadV :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i N →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i)) (value i))
  (hvalues :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i N →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (value i)) lim.word)
  (htarget : @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup target) lim.word),
  Light.Meets lim P p d
    (@List.cons.{0} Int target
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt indices)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N) (@List.nil.{0} Int))))))
    μ (ThreeSum.LightReportingBucketRow.time n) fun (r : Int) (ν : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightReportingBucketRow.count target value index n)))
      (@Eq.{1} (Nat → Int) ν μ) := by
  sorry
