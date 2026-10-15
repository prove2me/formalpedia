-- Prove2me | Theorems.Thm_ThreeSum_LightSourceRowFlag_meets
-- name    : ThreeSum.LightSourceRowFlag.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:37:31.604964+00:00
-- url     : https://prove2.me/theorems/8efdf8f3-61f6-4c1c-a3a8-3777c10fbf3c
-- title:
--   Verified independent trimming flags for both orientations of one row
-- statement:
--   Let $b_i\in\{0,1\}$ and $w_0(i),w_1(i)\le U$ for $i<L$, with $h\le L$ and modulus $p>0$. Let bucket tables $H_L,H_R:[p]\to\mathbb N$ be bounded by $V$, and let $c$ be the trimming cap. Suppose memory stores the bit row, both weight rows, and both bucket tables in segments ending at or before $f$, with $z+2\le f$. Assume $S\le W$, $d<D$, $f+\lfloor\log_2(LU+1)\rfloor+5\le S$, and $(L+1)(U+1)+4LU+4p+2L+V+c+19\le W$. If $P$ contains the row-flag body and its scan, remainder, and flag-test helpers, it stores
--
--   $$
--   \begin{aligned}
--   \nu(z)&=\mathbf1_{\sum b_i=h\,\land\,H_L((\sum w_{b_i}(i))\bmod p)\le c},\\
--   \nu(z+1)&=\mathbf1_{\sum b_i=h\,\land\,H_R((\sum w_{1-b_i}(i))\bmod p)\le c}.
--   \end{aligned}
--   $$
--
--   All sums range over $i<L$. The time is at most $150L+2R_{LU}+310$, where $R_v=43(\lfloor\log_2(v+1)\rfloor+1)+34$; memory below $f$ outside the two outputs is preserved. This constructs separate endpoint-retention flags.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceRowFlag.lean#L50-L162

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_emod_meets
import Theorems.Thm_ThreeSum_LightSourceFlagTest_meets
import Theorems.Thm_ThreeSum_LightSourceRowScan_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightSourceRowFlag.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain pRow pEmod pFlag : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightSourceRowFlag.body pRow pEmod pFlag)))
  (hrow :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pRow)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSourceRowScan.body))
  (hem :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pEmod)
      (@Option.some.{0} Light.Stmt Light.emodBody))
  (hflag :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pFlag)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSourceFlagTest.body))
  {μ : Nat → Int} {src src0 src1 L h histL histR p cap dst work U V : Nat} (bits w0 w1 leftCount rightCount : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hh : @LE.le.{0} Nat instLENat h L)
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src L) work)
  (hsrc0 : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src0 L) work)
  (hsrc1 : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src1 L) work)
  (hleft : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL p) work)
  (hright : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR p) work)
  (hdst :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      work)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightSourceRowFlag.space work L U) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceRowFlag.word L p U V cap))
      lim.word)
  (hbits :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i L →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i))
          (@Nat.cast.{0} Int instNatCastInt (bits i)))
  (hread0 :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i L →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src0 i))
          (@Nat.cast.{0} Int instNatCastInt (w0 i)))
  (hread1 :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i L →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src1 i))
          (@Nat.cast.{0} Int instNatCastInt (w1 i)))
  (hbitBound :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i L →
        @LE.le.{0} Nat instLENat (bits i) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hbound0 : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (w0 i) U)
  (hbound1 : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (w1 i) U)
  (hcountL :
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r p →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL r))
          (@Nat.cast.{0} Int instNatCastInt (leftCount r)))
  (hcountR :
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r p →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR r))
          (@Nat.cast.{0} Int instNatCastInt (rightCount r)))
  (hcountBoundL : ∀ (r : Nat), @LT.lt.{0} Nat instLTNat r p → @LE.le.{0} Nat instLENat (leftCount r) V)
  (hcountBoundR : ∀ (r : Nat), @LT.lt.{0} Nat instLTNat r p → @LE.le.{0} Nat instLENat (rightCount r) V),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src0)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src1)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt histL)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt histR)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cap)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work) (@List.nil.{0} Int))))))))))))
    μ (ThreeSum.LightSourceRowFlag.time L U) fun (x : Int) (ν : Nat → Int) =>
    And
      (@Eq.{1} Int (ν dst)
        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceRowFlag.flag L h p cap bits w0 w1 leftCount)))
      (And
        (@Eq.{1} Int
          (ν
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceRowFlag.flag L h p cap bits w1 w0 rightCount)))
        (Light.KeptBut μ ν work dst (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  sorry
