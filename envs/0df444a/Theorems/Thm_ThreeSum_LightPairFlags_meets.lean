-- Prove2me | Theorems.Thm_ThreeSum_LightPairFlags_meets
-- name    : ThreeSum.LightPairFlags.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:33:45.576571+00:00
-- url     : https://prove2.me/theorems/032d46f6-ab81-4db0-a273-00d411be96c4
-- title:
--   Verified construction of all local pair keys and trimming flags
-- statement:
--   Let $n,p>0$, let $b_i\in\{0,1\}^L$, and let $\ell_i,r_i<p$ for $i<n$. Let $H_L,H_R:[p]\to\mathbb N$ be supplied count tables bounded by $n$, and let $c$ be a cutoff. Suppose memory stores the bit matrix, both code arrays, and both count tables in segments ending at or before destination $z$. Assume $z+2n^2\le S\le W$, $100(n^2+p^2+c+L+n+p+1)\le W$, and $d<D$. If $P$ contains the pair constructor and its division, Boolean-dot, and trimming helpers, execution takes at most $n^2(20n+32L+412)+30$ steps and, for $i,j<n$, stores
--
--   $$
--   \begin{aligned}
--   \mu'(z+in+j)&=p\ell_i+r_j,\\
--   \mu'(z+n^2+in+j)&=\mathbf1_{\langle b_i,b_j\rangle=0\,\land\,H_L(\ell_i)\le c\,\land\,H_R(r_j)\le c}.
--   \end{aligned}
--   $$
--
--   Memory outside the two output arrays is preserved. This constructs the literal key and retained-pair tables used by the local cover matrix.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightPairFlags.lean#L57-L242

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
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_ThreeSum_LightBooleanDot_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_meets
import Theorems.Thm_ThreeSum_LightTrimTest_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightPairFlags.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain pDivide pDot pTrim : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightPairFlags.body pDivide pDot pTrim)))
  (hdivide :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pDivide)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSmallDivide.body))
  (hdot :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pDot)
      (@Option.some.{0} Light.Stmt ThreeSum.LightBooleanDot.body))
  (htrim :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pTrim)
      (@Option.some.{0} Light.Stmt ThreeSum.LightTrimTest.body))
  {μ : Nat → Int} {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap : Nat} (bits : Nat → Nat → Nat)
  (left right leftCount rightCount : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hbits :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitPtr
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n L))
      dst)
  (hleft : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) leftPtr n) dst)
  (hright : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rightPtr n) dst)
  (hleftHist :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) leftHist p) dst)
  (hrightHist :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rightHist p) dst)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
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
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cap) (@List.nil.{0} Int)))))))))))
    μ (ThreeSum.LightPairFlags.time L n) fun (x : Int) (μ' : Nat → Int) =>
    And
      (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n) →
          @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst i))
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightPairFlags.pairKey n p left right i)))
      (And
        (∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n) →
            @Eq.{1} Int
              (μ'
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n))
                  i))
              (@Nat.cast.{0} Int instNatCastInt
                (ThreeSum.LightPairFlags.pairFlag L n cap bits left right leftCount rightCount i)))
        (Light.SameOutside μ μ' dst
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n)))) := by
  sorry
