-- Prove2me | Theorems.Thm_ThreeSum_LightLocalKeys_Procs_meets
-- name    : ThreeSum.LightLocalKeys.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:14:53.633317+00:00
-- url     : https://prove2.me/theorems/2c838fca-5eb1-4c08-a846-09075befc1a6
-- title:
--   Construct every signed local key for every schedule row
-- statement:
--   Let $n$ stored masks satisfy $m_i<2^L$, and let $R$ stored coefficient pairs $w^0_j,w^1_j$ have natural entries at most $U$. Masks and coefficient rows end by destination $z$, the $Rn$-cell output ends by reusable scratch $f$, and the local-row space and full word budgets fit the machine limits. Assume space fits in a word and $d+L+3$ fits in the depth limit. The installed routines produce
--   $$
--   \mu'(z+jn+i)=\sum_{a<L:\,\operatorname{bit}(m_i,a)=0}
--   \bigl(w^1_j(a)-w^0_j(a)\bigr)
--   \quad(j<R,\ i<n).
--   $$
--   They preserve memory below $z$ and use $R(\operatorname{rowTime}(L,n)+\operatorname{copyTime}(n)+130)+20$ steps.
--
--   This creates the complete occurrence-by-output array of signed local keys.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalKeys.lean#L45-L129

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
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
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_Light_Ends_pass
import Theorems.Thm_ThreeSum_LightLocalKeyRow_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightLocalKeys.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightLocalKeys.Procs P pMain) {μ : Nat → Int}
  {L masks n maps rows dst free U : Nat} (mask : Nat → Nat) (wFalse wTrue : Nat → Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      lim.depth)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightLocalKeyRow.space free L n) lim.space)
  (hmasks : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks n) dst)
  (hmaps :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) rows
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)))
      dst)
  (hdst :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) rows n))
      free)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalKeys.word L U rows)) lim.word)
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
  (hreadFalse :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j rows →
        ∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i L →
            @Eq.{1} Int
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) j
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)))
                  i))
              (@Nat.cast.{0} Int instNatCastInt (wFalse j i)))
  (hreadTrue :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j rows →
        ∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i L →
            @Eq.{1} Int
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) j
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)))
                    L)
                  i))
              (@Nat.cast.{0} Int instNatCastInt (wTrue j i)))
  (hboundFalse :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j rows →
        ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (wFalse j i) U)
  (hboundTrue :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j rows →
        ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (wTrue j i) U),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masks)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maps)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rows)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int))))))))
    μ (ThreeSum.LightLocalKeys.time L n rows) fun (x : Int) (ν : Nat → Int) =>
    And
      (∀ (j : Nat),
        @LT.lt.{0} Nat instLTNat j rows →
          ∀ (i : Nat),
            @LT.lt.{0} Nat instLTNat i n →
              @Eq.{1} Int
                (ν
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) j n))
                    i))
                (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                  (@Nat.cast.{0} Int instNatCastInt
                    (ThreeSum.OneHotMask.eval (wTrue j)
                      (fun (x : Nat) => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) L (mask i)))
                  (@Nat.cast.{0} Int instNatCastInt
                    (ThreeSum.OneHotMask.eval (wFalse j)
                      (fun (x : Nat) => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) L (mask i)))))
      (Light.Kept μ ν dst) := by
  sorry
