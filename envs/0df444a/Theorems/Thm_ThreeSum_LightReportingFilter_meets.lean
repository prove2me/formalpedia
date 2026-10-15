-- Prove2me | Theorems.Thm_ThreeSum_LightReportingFilter_meets
-- name    : ThreeSum.LightReportingFilter.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:05:06.515874+00:00
-- url     : https://prove2.me/theorems/aecd7764-b352-4a6a-9cc3-b098445e56dc
-- title:
--   Verified extraction of indices with positive counts
-- statement:
--   Let $c:\mathbb N\to\mathbb N$ be a length-$n$ count array stored in memory $\mu$ at address $A$, with $c(i)\le\mathrm{word}$ for every $i<n$. Assume the source interval $[A,A+n)$ and destination interval $[B,B+n)$ are disjoint, both fit within $\mathrm{space}\le\mathrm{word}$, and the Light program contains the reporting-filter body.
--
--   Define the ordered list $L=[i\mid 0\le i<n,\ c(i)>0]$. The call with arguments $(n,A,B)$ terminates within $100n+40$ steps and satisfies
--   $$
--   r=|L|,\qquad \nu(B+j)=L_j\quad(j<|L|).
--   $$
--   Every memory cell outside $[B,B+n)$ is preserved.
--
--   This converts positive count entries into a compact list of their original indices.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingFilter.lean#L59-L110

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
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightReportingFilter.meets : ∀ {lim : Light.Limits} {P : Light.Program} {p n src dst d : Nat} {μ : Nat → Int} (count : Nat → Nat)
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt ThreeSum.LightReportingFilter.body))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) lim.space)
  (hdst : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst n) lim.space)
  (hsep : Light.Apart src n dst n)
  (hword :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n → @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (count i)) lim.word)
  (hread :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i))
          (@Nat.cast.{0} Int instNatCastInt (count i))),
  Light.Meets lim P p d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst) (@List.nil.{0} Int))))
    μ (ThreeSum.LightReportingFilter.time n) fun (r : Int) (μ' : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Nat (ThreeSum.LightReportingFilter.selected count n))))
      (And (Light.SegN μ' dst (ThreeSum.LightReportingFilter.selected count n)) (Light.SameOutside μ μ' dst n)) := by
  sorry
