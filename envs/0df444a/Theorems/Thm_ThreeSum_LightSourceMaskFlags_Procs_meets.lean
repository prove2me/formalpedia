-- Prove2me | Theorems.Thm_ThreeSum_LightSourceMaskFlags_Procs_meets
-- name    : ThreeSum.LightSourceMaskFlags.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:18:18.067198+00:00
-- url     : https://prove2.me/theorems/8570ae91-102b-456d-8344-e834d9ffa85a
-- title:
--   Compute independent global trimming flags from a mask
-- statement:
--   Let $m<2^{JL}$ be a global mask, with $h\le L$ and positive modulus $p$. Memory contains $J$ selected occurrence indices, their valid candidate indices, coefficient rows bounded by $U$, and two candidate bucket-count tables bounded by $V$. These inputs and the two-cell output end before bit scratch; reserve $JL$ bit cells, two row cells, and the specified arithmetic scratch in order. Assume the program's space and word budgets fit, space fits in a word, and $d+JL+3$ fits in depth. For each block, let $F^L_j$ test cardinality $h$ and the left bucket cap, and let $F^R_j$ use swapped coefficients and the right table. The program writes
--   $$
--   \mu'(z)=\prod_{j<J}F^L_j,\qquad \mu'(z+1)=\prod_{j<J}F^R_j.
--   $$
--   It satisfies the bit-decoding-plus-trimming time budget and preserves memory below bit scratch outside these two output cells.
--
--   This constructs both endpoint flags from the actual global mask.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceMaskFlags.lean#L46-L137

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
import Theorems.Thm_ThreeSum_LightMaskBits_meets
import Theorems.Thm_ThreeSum_LightSourceTrim_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct

theorem ThreeSum.LightSourceMaskFlags.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightSourceMaskFlags.Procs P pMain)
  {μ : Nat → Int} {J L h p cap occ maps candidates histL histR mask dst bitBase rowOut work U V M K : Nat}
  (sel candidate : Nat → Nat) (w0 w1 leftCount rightCount : Nat → Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      lim.depth)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hh : @LE.le.{0} Nat instLENat h L)
  (hocc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ J) bitBase)
  (hmaps :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
          M))
      bitBase)
  (hcandidates :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) candidates M) bitBase)
  (hleft :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) K p))
      bitBase)
  (hright :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) K p))
      bitBase)
  (hdst :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
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
  (hmask :
    @LT.lt.{0} Nat instLTNat mask
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L)))
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
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt mask)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bitBase)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rowOut)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                  (@List.nil.{0} Int))))))))))))))))
    μ (ThreeSum.LightSourceMaskFlags.time J L U) fun (x : Int) (ν : Nat → Int) =>
    And
      (@Eq.{1} Int (ν dst)
        (@Nat.cast.{0} Int instNatCastInt
          (ThreeSum.SourceFlagProduct.product
            (ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate
              (ThreeSum.LightMaskBits.bit (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L) mask) w0
              w1 leftCount)
            J)))
      (And
        (@Eq.{1} Int
          (ν
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Nat.cast.{0} Int instNatCastInt
            (ThreeSum.SourceFlagProduct.product
              (ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate
                (ThreeSum.LightMaskBits.bit (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L) mask)
                w1 w0 rightCount)
              J)))
        (Light.KeptBut μ ν bitBase dst (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  sorry
