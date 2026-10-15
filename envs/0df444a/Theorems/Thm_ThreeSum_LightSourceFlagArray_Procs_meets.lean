-- Prove2me | Theorems.Thm_ThreeSum_LightSourceFlagArray_Procs_meets
-- name    : ThreeSum.LightSourceFlagArray.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:30:46.996005+00:00
-- url     : https://prove2.me/theorems/51a877e5-67fd-4a99-9d1f-0d8ec43e4809
-- title:
--   Constructing independent endpoint flags for every stored mask
-- statement:
--   Fix $p>0$, $h\le L$, and $J$ selected occurrences $s_j<M$, each mapped to a candidate $c(s_j)<K$. Memory stores these selectors, two coefficient rows per occurrence bounded by $U$, two $K\times p$ count tables bounded by $V$, and $n$ masks $q_i<2^{JL}$. For each block, a mask orientation passes when its block has $h$ set bits and its one-hot hash residue indexes a count at most the cap. Define $F_L(q)$ as the product of these block flags, and $F_R(q)$ using the swapped coefficients and right counts.
--
--   All inputs end before $a$; require $a+2n+2\le b$, $b+JL\le r$, $r+2\le w$, the specified single-mask scratch and word budgets, $S\le W$, and $d+JL+4\le D$. The stated procedures write
--   $$\nu(a+i)=F_L(q_i),\qquad\nu(a+n+i)=F_R(q_i)\quad(i<n)$$
--   within $n(T_{\mathrm{mask}}(J,L,U)+200)+10$ steps. Below $b$, only the $2n+2$-cell output/work interval may change.
--
--   This retains both endpoint decisions independently for later bucket selection.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceFlagArray.lean#L56-L187

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
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Theorems.Thm_ThreeSum_LightSourceMaskFlags_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct

theorem ThreeSum.LightSourceFlagArray.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightSourceFlagArray.Procs P pMain)
  {μ : Nat → Int} {J L h p cap occ maps candidates histL histR masks n dst bitBase rowOut work U V M K : Nat}
  (sel candidate mask : Nat → Nat) (w0 w1 leftCount rightCount : Nat → Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      lim.depth)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hh : @LE.le.{0} Nat instLENat h L)
  (hocc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ J) dst)
  (hmaps :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
          M))
      dst)
  (hcandidates :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) candidates M) dst)
  (hleft :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) K p))
      dst)
  (hright :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) K p))
      dst)
  (hmasks : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks n) dst)
  (hdst :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      bitBase)
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
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightSourceMaskFlags.space work J L U) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceMaskFlags.word J L p U V cap))
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
        ∀ (r : Nat), @LT.lt.{0} Nat instLTNat r p → @LE.le.{0} Nat instLENat (rightCount k r) V)
  (hmaskRead :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks i))
          (@Nat.cast.{0} Int instNatCastInt (mask i)))
  (hmaskBound :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LT.lt.{0} Nat instLTNat (mask i)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))),
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
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masks)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bitBase)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rowOut)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                    (@List.nil.{0} Int)))))))))))))))))
    μ (ThreeSum.LightSourceFlagArray.time n J L U) fun (x : Int) (ν : Nat → Int) =>
    And
      (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i n →
          @Eq.{1} Int (ν (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst i))
            (@Nat.cast.{0} Int instNatCastInt
              (ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w0 w1 leftCount (mask i))))
      (And
        (∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i n →
            @Eq.{1} Int
              (ν
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst n) i))
              (@Nat.cast.{0} Int instNatCastInt
                (ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w1 w0 rightCount (mask i))))
        (Light.KeptBut μ ν bitBase dst
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) := by
  sorry
