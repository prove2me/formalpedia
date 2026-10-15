-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_recurse_ends
-- name    : ThreeSum.LightKaratsuba.recurse_ends
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:12:40.681295+00:00
-- url     : https://prove2.me/theorems/08325a2f-74e6-46e3-b7bc-7e8f6edef319
-- title:
--   Karatsuba’s recursive body implements the induction step
-- statement:
--   Let $m=2^k$ and let integer coefficient lists $A,B$ each have length $2m$ and coefficients bounded in absolute value by $U$. Their memory segments and the $4m$-cell output end by scratch base $f$. Assume $f+16m$ fits in space, $128(2m)^3(U+1)^2$ fits in a word, space fits in a word, and $d$ is below the depth limit. Suppose every size-$m$ recursive call at depth $d+1$ satisfies the stated multiplication contract under its own layout and word bounds. Then the recursive body yields
--   $$
--   \mu'(z+j)=[X^j](A(X)B(X))\quad(j<4m)
--   $$
--   within $T(k+1)-4$ steps, where $T(0)=30$ and $T(k+1)=3T(k)+2500\,2^k$. Below $f$, only the output may change.
--
--   This is the executable induction step for the fixed Karatsuba procedure.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightKaratsuba.lean#L435-L571

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
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
import Theorems.Thm_Light_half_meets
import Theorems.Thm_ThreeSum_Karatsuba_product_coeff_bound
import Theorems.Thm_ThreeSum_LightArray_linear_bounded_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_join_ends
import Theorems.Thm_ThreeSum_LightKaratsuba_joined_product


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightKaratsuba.recurse_ends : ∀ {lim : Light.Limits} {P : Light.Program} {pSelf pHalf pLinear pFill : Nat}
  (C : ThreeSum.LightKaratsuba.Procs P pSelf pHalf pLinear pFill) {d k m a b out work U : Nat} {as bs : List.{0} Int}
  {μ : Nat → Int}
  (hmPow :
    @Eq.{1} Nat m
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hAlen :
    @Eq.{1} Nat (@List.length.{0} Int as)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
  (hBlen :
    @Eq.{1} Nat (@List.length.{0} Int bs)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
  (hAseg : Light.Seg μ a as) (hBseg : Light.Seg μ b bs)
  (hA : ThreeSum.Karatsuba.CoeffBound as (@Nat.cast.{0} Int instNatCastInt U))
  (hB : ThreeSum.Karatsuba.CoeffBound bs (@Nat.cast.{0} Int instNatCastInt U))
  (haf :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
      work)
  (hbf :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
      work)
  (hof :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) out
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
      work)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (ThreeSum.LightKaratsuba.wordBound
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          U))
      lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (ih :
    ∀ (a' b' out' work' U' : Nat) (as' bs' : List.{0} Int) (μ' : Nat → Int),
      @Eq.{1} Nat (@List.length.{0} Int as') m →
        @Eq.{1} Nat (@List.length.{0} Int bs') m →
          Light.Seg μ' a' as' →
            Light.Seg μ' b' bs' →
              ThreeSum.Karatsuba.CoeffBound as' (@Nat.cast.{0} Int instNatCastInt U') →
                ThreeSum.Karatsuba.CoeffBound bs' (@Nat.cast.{0} Int instNatCastInt U') →
                  @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a' m)
                      work' →
                    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b' m)
                        work' →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) out'
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          work' →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work'
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) m))
                            lim.space →
                          @LE.le.{0} Int Int.instLEInt
                              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightKaratsuba.wordBound m U')) lim.word →
                            Light.Meets lim P pSelf
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt m)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a')
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b')
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt out')
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work')
                                        (@List.nil.{0} Int))))))
                              μ' (ThreeSum.LightKaratsuba.time k) fun (x : Int) (μ'' : Nat → Int) =>
                              ThreeSum.LightKaratsuba.Result μ' out' m work' as' bs' μ''),
  Light.Ends lim P d (ThreeSum.LightKaratsuba.recurseBody pSelf pHalf pLinear pFill)
    {
      loc :=
        Light.frame
          (@List.cons.{0} Int
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) (@Nat.cast.{0} Int instNatCastInt m))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt out)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work) (@List.nil.{0} Int)))))),
      mem := μ }
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
      (ThreeSum.LightKaratsuba.time
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
    fun (σ' : Light.State) =>
    ThreeSum.LightKaratsuba.Result μ out
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
      work as bs σ'.mem := by
  sorry
