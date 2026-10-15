-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverCandidate_Procs_meets
-- name    : ThreeSum.LightLocalCoverCandidate.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:17:43.77686+00:00
-- url     : https://prove2.me/theorems/ce89205f-a344-4d60-b151-38fa4a80cf6f
-- title:
--   Construct one local candidate’s coefficients, histograms, and support row
-- statement:
--   Fix $L$, positive $n,p$, a cap, and a candidate index. Store $n$ masks below $2^L$ and an $n\times L$ Boolean matrix. Let $w_0,w_1$ be the even and odd radix-$p$ digits of the candidate's $2L$-digit encoding. Reserve, in order, both coefficient rows, two $2n$ raw/residue buffers, two $p$-cell histograms, and a $p^2$-cell destination before scratch. Assume the explicit space and word budgets fit, space fits in a word, and $d+L+4$ fits in depth. The installed program stores the decoded coefficients and exact histograms for the ordinary and swapped hash codes. For every $r<p^2$, its destination satisfies
--   $$
--   \mu'(z+r)=1\iff\exists i,j<n:\ p\,\ell_i+r_j=r,
--   \ \langle b_i,b_j\rangle=0,
--   \ H_L(\ell_i),H_R(r_j)\le\mathrm{cap}.
--   $$
--   All other entries are zero. Here the codes use the stored masks and the dot product uses the supplied Boolean rows. The explicit time and region-preservation contracts support the outer candidate loop.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverCandidate.lean#L57-L200

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_LightLocalCoverHashHistogram_meets
import Theorems.Thm_ThreeSum_LightLocalCoverRow_Procs_meets
import Theorems.Thm_ThreeSum_LightWeightDecode_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments

theorem ThreeSum.LightLocalCoverCandidate.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightLocalCoverCandidate.Procs P pMain)
  {μ : Nat → Int} {L n p cap index masks bitPtr coef raw0 raw1 hist0 hist1 dst work : Nat} (mask w0 w1 : Nat → Nat)
  (bits : Nat → Nat → Nat) (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      lim.depth)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightLocalCoverCandidate.space work L n p) lim.space)
  (hmasks : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks n) coef)
  (hbits :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitPtr
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n L))
      coef)
  (hcoef :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) coef
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L))
      raw0)
  (hraw0 :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw0
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      raw1)
  (hraw1 :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw1
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      hist0)
  (hhist0 : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist0 p) hist1)
  (hhist1 : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist1 p) dst)
  (hdst :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p p))
      work)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalCoverCandidate.word L n p cap index)) lim.word)
  (hmaskRead :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks i))
          (@Nat.cast.{0} Int instNatCastInt (mask i)))
  (hmaskLt :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LT.lt.{0} Nat instLTNat (mask i)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L))
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
  (hw0 :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i L →
        @Eq.{1} Nat (w0 i)
          (ThreeSum.WeightEnumeration.digit p
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
            index
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i)))
  (hw1 :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i L →
        @Eq.{1} Nat (w1 i)
          (ThreeSum.WeightEnumeration.digit p
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
            index
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt index)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cap)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masks)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bitPtr)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt coef)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt raw0)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt raw1)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt hist0)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt hist1)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                (@List.nil.{0} Int)))))))))))))))
    μ (ThreeSum.LightLocalCoverCandidate.time L n p index) fun (x : Int) (μ' : Nat → Int) =>
    And (ThreeSum.LightWeightDecode.Rows μ' coef L p index)
      (And
        (∀ (r : Nat),
          @LT.lt.{0} Nat instLTNat r p →
            And
              (@Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist0 r))
                (@Nat.cast.{0} Int instNatCastInt
                  (ThreeSum.LightHistogram.count (ThreeSum.LightHashHistogram.code L p mask w0 w1) r n)))
              (@Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist1 r))
                (@Nat.cast.{0} Int instNatCastInt
                  (ThreeSum.LightHistogram.count (ThreeSum.LightHashHistogram.code L p mask w1 w0) r n))))
        (And
          (∀ (r : Nat),
            @LT.lt.{0} Nat instLTNat r (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p p) →
              @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst r))
                (@Nat.cast.{0} Int instNatCastInt
                  (ThreeSum.LightLocalCoverCandidate.entry L n p cap mask bits w0 w1 r)))
          (ThreeSum.LightLocalCoverCandidate.Preserved μ μ' work coef raw0 raw1 hist0 hist1 dst L n p))) := by
  sorry
