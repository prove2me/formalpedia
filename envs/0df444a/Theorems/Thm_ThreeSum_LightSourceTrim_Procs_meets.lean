-- Prove2me | Theorems.Thm_ThreeSum_LightSourceTrim_Procs_meets
-- name    : ThreeSum.LightSourceTrim.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:04:47.00567+00:00
-- url     : https://prove2.me/theorems/4fd44d55-8ab9-4a2a-bc89-b8d18e2bbea2
-- title:
--   Execution contract for trimming a source across all blocks
-- statement:
--   Consider $J$ bit rows of length $L$, a required weight $h\le L$, and a positive modulus $p$. Each row selects one of $M$ pairs of weight rows, whose entries are at most $U$; that selection chooses one of $K$ left and right histograms, bounded by $V$. Assume memory stores these arrays exactly, all selection indices are valid, and all bits are Boolean. Their reserved intervals end before the two-cell row-result buffer at $r$; the final two-cell output ends by $r$, and scratch starts at $f\ge r+2$. Require $S\le W$, $d+1<D$, $f+\lfloor\log_2(LU+1)\rfloor+5\le S$, and $(L+1)(U+1)+4LU+4p+2L+V+\mathrm{cap}+19\le W$.
--
--   Let $F_j^\ell,F_j^r$ be the row flags: the row has $h$ ones and its corresponding residue bucket contains at most $\mathrm{cap}$ elements, with the two weight rows interchanged for the right flag. The specified procedures write
--   $$\nu(a)=\prod_{j<J}F_j^\ell,\qquad\nu(a+1)=\prod_{j<J}F_j^r.$$
--   They take at most $J(150L+2R_{LU}+560)+100$ steps, where $R_z=43(\lfloor\log_2(z+1)\rfloor+1)+34$, and preserve memory below $r$ outside the output.
--
--   The products implement simultaneous acceptance over every block.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceTrim.lean#L76-L233

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_ThreeSum_LightSourceRowFlag_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct

theorem ThreeSum.LightSourceTrim.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightSourceTrim.Procs P pMain) {μ : Nat → Int}
  {J L h p cap occ maps candidates histL histR bitBase rowOut work dst U V M K : Nat} (sel candidate bits : Nat → Nat)
  (w0 w1 leftCount rightCount : Nat → Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      lim.depth)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hh : @LE.le.{0} Nat instLENat h L)
  (hocc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ J) rowOut)
  (hmaps :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
          M))
      rowOut)
  (hcandidates :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) candidates M) rowOut)
  (hleft :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) K p))
      rowOut)
  (hright :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) K p))
      rowOut)
  (hbits :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitBase
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))
      rowOut)
  (hrowOut :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rowOut
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      work)
  (hdst :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      rowOut)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightSourceRowFlag.space work L U) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceRowFlag.word L p U V cap))
      lim.word)
  (hsel : ∀ (j : Nat), @LT.lt.{0} Nat instLTNat j J → @LT.lt.{0} Nat instLTNat (sel j) M)
  (hcandidate : ∀ (s : Nat), @LT.lt.{0} Nat instLTNat s M → @LT.lt.{0} Nat instLTNat (candidate s) K)
  (hoccRead :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j J →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ j))
          (@Nat.cast.{0} Int instNatCastInt (sel j)))
  (hcandidateRead :
    ∀ (s : Nat),
      @LT.lt.{0} Nat instLTNat s M →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) candidates s))
          (@Nat.cast.{0} Int instNatCastInt (candidate s)))
  (hbitsRead :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L) →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitBase i))
          (@Nat.cast.{0} Int instNatCastInt (bits i)))
  (hbitBound :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L) →
        @LE.le.{0} Nat instLENat (bits i) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hread0 :
    ∀ (s : Nat),
      @LT.lt.{0} Nat instLTNat s M →
        ∀ (a : Nat),
          @LT.lt.{0} Nat instLTNat a L →
            @Eq.{1} Int
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                      s))
                  a))
              (@Nat.cast.{0} Int instNatCastInt (w0 s a)))
  (hread1 :
    ∀ (s : Nat),
      @LT.lt.{0} Nat instLTNat s M →
        ∀ (a : Nat),
          @LT.lt.{0} Nat instLTNat a L →
            @Eq.{1} Int
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                        s))
                    L)
                  a))
              (@Nat.cast.{0} Int instNatCastInt (w1 s a)))
  (hbound0 :
    ∀ (s : Nat),
      @LT.lt.{0} Nat instLTNat s M → ∀ (a : Nat), @LT.lt.{0} Nat instLTNat a L → @LE.le.{0} Nat instLENat (w0 s a) U)
  (hbound1 :
    ∀ (s : Nat),
      @LT.lt.{0} Nat instLTNat s M → ∀ (a : Nat), @LT.lt.{0} Nat instLTNat a L → @LE.le.{0} Nat instLENat (w1 s a) U)
  (hcountL :
    ∀ (k : Nat),
      @LT.lt.{0} Nat instLTNat k K →
        ∀ (r : Nat),
          @LT.lt.{0} Nat instLTNat r p →
            @Eq.{1} Int
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) k p))
                  r))
              (@Nat.cast.{0} Int instNatCastInt (leftCount k r)))
  (hcountR :
    ∀ (k : Nat),
      @LT.lt.{0} Nat instLTNat k K →
        ∀ (r : Nat),
          @LT.lt.{0} Nat instLTNat r p →
            @Eq.{1} Int
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) k p))
                  r))
              (@Nat.cast.{0} Int instNatCastInt (rightCount k r)))
  (hcountBoundL :
    ∀ (k : Nat),
      @LT.lt.{0} Nat instLTNat k K →
        ∀ (r : Nat), @LT.lt.{0} Nat instLTNat r p → @LE.le.{0} Nat instLENat (leftCount k r) V)
  (hcountBoundR :
    ∀ (k : Nat),
      @LT.lt.{0} Nat instLTNat k K →
        ∀ (r : Nat), @LT.lt.{0} Nat instLTNat r p → @LE.le.{0} Nat instLENat (rightCount k r) V),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cap)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt occ)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maps)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt candidates)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt histL)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt histR)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bitBase)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rowOut)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                                (@List.nil.{0} Int)))))))))))))))
    μ (ThreeSum.LightSourceTrim.time J L U) fun (x : Int) (ν : Nat → Int) =>
    And
      (@Eq.{1} Int (ν dst)
        (@Nat.cast.{0} Int instNatCastInt
          (ThreeSum.SourceFlagProduct.product
            (ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w0 w1 leftCount) J)))
      (And
        (@Eq.{1} Int
          (ν
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Nat.cast.{0} Int instNatCastInt
            (ThreeSum.SourceFlagProduct.product
              (ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w1 w0 rightCount) J)))
        (Light.KeptBut μ ν rowOut dst (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  sorry
