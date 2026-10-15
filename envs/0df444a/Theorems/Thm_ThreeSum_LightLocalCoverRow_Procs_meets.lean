-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverRow_Procs_meets
-- name    : ThreeSum.LightLocalCoverRow.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:56:21.425217+00:00
-- url     : https://prove2.me/theorems/50f7b20f-1811-42a3-b83a-4221a8c191b9
-- title:
--   Constructing a retained local-cover support row
-- statement:
--   Let $n,p>0$. Memory stores Boolean rows $b_i$ of width $L$, labels $\ell_i,r_i<p$, and two arbitrary count arrays $c_L,c_R\le n$ of length $p$. Let $K$ be a cap. All inputs and the destination row of length $p^2$ end before scratch base $w$. Assume the specified pair-test and support-marking procedures, $w+2n^2\le S\le B$, $d+1<D$, and
--   $$100(n^2+p^2+K+L+n+p+1)\le B.$$
--   For each $z<p^2$, the output is
--   $$\nu(a+z)=\mathbf1\!\left[\exists i,j<n:\ \ell_ip+r_j=z,\ \sum_{u<L}b_i(u)b_j(u)=0,\ c_L(\ell_i)\le K,\ c_R(r_j)\le K\right].$$
--   The routine takes at most $n^2(20n+32L+452)+13p^2+152$ steps and preserves cells below $w$ outside this row.
--
--   This builds the support of the retained pair keys, collapsing repeated representations of the same key to one Boolean entry.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverRow.lean#L41-L106

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
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
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
import Theorems.Thm_ThreeSum_LightPairFlags_meets
import Theorems.Thm_ThreeSum_LightSupportMark_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightLocalCoverRow.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightLocalCoverRow.Procs P pMain)
  {μ : Nat → Int} {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap keys : Nat} (bits : Nat → Nat → Nat)
  (left right leftCount rightCount : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      lim.depth)
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hbits :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitPtr
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n L))
      keys)
  (hleft : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) leftPtr n) keys)
  (hright : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rightPtr n) keys)
  (hleftHist :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) leftHist p) keys)
  (hrightHist :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rightHist p) keys)
  (hdst :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p p))
      keys)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keys
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n)))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightPairFlags.word L n p cap)) lim.word)
  (hbitsRead :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        ∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j L →
            @Eq.{1} Int
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitPtr
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i L))
                  j))
              (@Nat.cast.{0} Int instNatCastInt (bits i j)))
  (hbitsValue :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        ∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j L →
            @LE.le.{0} Nat instLENat (bits i j) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hleftRead :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) leftPtr i))
          (@Nat.cast.{0} Int instNatCastInt (left i)))
  (hrightRead :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rightPtr i))
          (@Nat.cast.{0} Int instNatCastInt (right i)))
  (hleftLt : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i n → @LT.lt.{0} Nat instLTNat (left i) p)
  (hrightLt : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i n → @LT.lt.{0} Nat instLTNat (right i) p)
  (hleftCount :
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r p →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) leftHist r))
          (@Nat.cast.{0} Int instNatCastInt (leftCount r)))
  (hrightCount :
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r p →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rightHist r))
          (@Nat.cast.{0} Int instNatCastInt (rightCount r)))
  (hleftBound : ∀ (r : Nat), @LT.lt.{0} Nat instLTNat r p → @LE.le.{0} Nat instLENat (leftCount r) n)
  (hrightBound : ∀ (r : Nat), @LT.lt.{0} Nat instLTNat r p → @LE.le.{0} Nat instLENat (rightCount r) n),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bitPtr)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt leftPtr)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rightPtr)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt leftHist)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rightHist)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cap)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt keys) (@List.nil.{0} Int))))))))))))
    μ (ThreeSum.LightLocalCoverRow.time L n p) fun (x : Int) (μ' : Nat → Int) =>
    And
      (∀ (r : Nat),
        @LT.lt.{0} Nat instLTNat r (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p p) →
          @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst r))
            (@Nat.cast.{0} Int instNatCastInt
              (ThreeSum.LightSupportMark.bit (ThreeSum.LightPairFlags.pairKey n p left right)
                (ThreeSum.LightPairFlags.pairFlag L n cap bits left right leftCount rightCount) r
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n))))
      (Light.KeptBut μ μ' keys dst (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p p)) := by
  sorry
