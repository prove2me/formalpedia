-- Prove2me | Theorems.Thm_ThreeSum_LightReportingGatherPair_program_meets
-- name    : ThreeSum.LightReportingGatherPair.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:32:48.479406+00:00
-- url     : https://prove2.me/theorems/e7ce242a-aecf-48c9-8c55-a3e11a67b681
-- title:
--   Gathering two aligned arrays with shared selection indices
-- statement:
--   Let memory $\mu$ store an index list $s_i<n$, $i<t$, and integer source arrays $\ell_j,r_j$, $j<n$, whose absolute values fit the word limit. Write $I,S_L,S_R$ for their addresses and $D_L,D_R$ for the two output addresses. All input and output intervals must fit within $\mathrm{space}\le\mathrm{word}$. Require the index interval to be disjoint from both outputs; the left output to be disjoint from both sources and the right output; and the right output to be disjoint from the right source. Suppose $d<\mathrm{depth}$.
--
--   The fixed two-procedure gather program, entered at procedure $1$, terminates within $80t+80$ steps and satisfies
--   $$
--   \nu(D_L+i)=\ell_{s_i},\qquad \nu(D_R+i)=r_{s_i}\quad(i<t).
--   $$
--   It preserves all memory outside the two length-$t$ output intervals.
--
--   This preserves alignment between the selected left and right reporting masks.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingGatherPair.lean#L18-L49

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
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Theorems.Thm_Light_Ends_pass


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightReportingGatherPair.program_meets : ∀ {lim : Light.Limits} {μ : Nat → Int} {indices srcL srcR dstL dstR t n d : Nat} (index : Nat → Nat)
  (left right : Nat → Int) (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hindices :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) indices t) lim.space)
  (hsrcL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcL n) lim.space)
  (hsrcR : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcR n) lim.space)
  (hdstL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dstL t) lim.space)
  (hdstR : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dstR t) lim.space)
  (hsepIL : Light.Apart indices t dstL t) (hsepIR : Light.Apart indices t dstR t) (hsepLL : Light.Apart srcL n dstL t)
  (hsepRL : Light.Apart srcR n dstL t) (hsepRR : Light.Apart srcR n dstR t) (hsepOut : Light.Apart dstL t dstR t)
  (hindex : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i t → @LT.lt.{0} Nat instLTNat (index i) n)
  (hreadI :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i t →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) indices i))
          (@Nat.cast.{0} Int instNatCastInt (index i)))
  (hreadL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcL i)) (left i))
  (hreadR :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcR i)) (right i))
  (hwordL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (left i)) lim.word)
  (hwordR :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (right i)) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth),
  Light.Meets lim ThreeSum.LightReportingGatherPair.program
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt indices)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcL)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcR)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt t)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dstL)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dstR) (@List.nil.{0} Int))))))))
    μ (ThreeSum.LightReportingGatherPair.time t) fun (x : Int) (ν : Nat → Int) =>
    And (Light.Seg ν dstL (@List.ofFn.{0} Int t fun (i : Fin t) => left (index (@Fin.val t i))))
      (And (Light.Seg ν dstR (@List.ofFn.{0} Int t fun (i : Fin t) => right (index (@Fin.val t i))))
        (Light.SameOutside2 μ ν dstL t dstR t)) := by
  sorry
