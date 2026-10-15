-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceHashes_Procs_meets
-- name    : ThreeSum.LightBlockSourceHashes.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:48:17.612178+00:00
-- url     : https://prove2.me/theorems/487a7912-b74f-4876-84d8-4c225a13e995
-- title:
--   Constructing both block-hash orientations and their coefficients
-- statement:
--   Let $p\ge1$, choose $J$ map occurrences $s_j<M$, and store two natural coefficient rows $w_0(s,\cdot),w_1(s,\cdot)$ of width $L$ for each occurrence, all bounded by $U$. Store also $n$ masks $q_i<2^{JL}$. Define $f_b(jL+a)=p^jw_b(s_j,a)$ for $j<J$, $a<L$, and $E(f,g,q)=\sum_{a<JL}(\operatorname{bit}_a(q)?g(a):f(a))$.
--
--   Assume the specified coefficient and mask-hash procedures. All occurrence, map, and mask inputs end before coefficient base $c_0$; require $c_0+JL\le c_1$, $c_1+JL\le r_L$, $r_L+n\le r_R$, $r_R+n\le w$, $w+\max(J+1,JL+1)\le S\le B$, $d+JL+2\le D$, and
--   $$p^{J+1}(U+1)+2^{JL+1}+(JL+1)p^JU\le B.$$
--   Within $200n(JL+1)+70JL+149J+475$ steps, the final arrays satisfy
--   $$\nu(c_b+a)=f_b(a),\quad\nu(r_L+i)=E(f_0,f_1,q_i),\quad\nu(r_R+i)=E(f_1,f_0,q_i).$$
--   Cells below $c_0$ are preserved.
--
--   This constructs both endpoint hash arrays from the selected block maps.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBlockSourceHashes.lean#L50-L141

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
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
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
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
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
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
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
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BlockCoefficientRows_rows_flat
import Theorems.Thm_ThreeSum_LightBlockCoefficients_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds

theorem ThreeSum.LightBlockSourceHashes.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightBlockSourceHashes.Procs P pMain)
  {μ : Nat → Int} {J L p occ maps coeff0 coeff1 masks rawLeft rawRight n work U M : Nat} (sel mask : Nat → Nat)
  (w0 w1 : Nat → Nat → Nat) (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hp : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) p)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      lim.depth)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightBlockSourceHashes.space work J L) lim.space)
  (hocc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ J) coeff0)
  (hmaps :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
          M))
      coeff0)
  (hmasks : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks n) coeff0)
  (hc0 :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) coeff0
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))
      coeff1)
  (hc1 :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) coeff1
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))
      rawLeft)
  (hleft :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawLeft n) rawRight)
  (hright : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawRight n) work)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockSourceHashes.word J L p U))
      lim.word)
  (hsel : ∀ (j : Nat), @LT.lt.{0} Nat instLTNat j J → @LT.lt.{0} Nat instLTNat (sel j) M)
  (hselRead :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j J →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ j))
          (@Nat.cast.{0} Int instNatCastInt (sel j)))
  (hread0 :
    ∀ (s : Nat),
      @LT.lt.{0} Nat instLTNat s M →
        ∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i L →
            @Eq.{1} Int
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                      s))
                  i))
              (@Nat.cast.{0} Int instNatCastInt (w0 s i)))
  (hread1 :
    ∀ (s : Nat),
      @LT.lt.{0} Nat instLTNat s M →
        ∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i L →
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
                  i))
              (@Nat.cast.{0} Int instNatCastInt (w1 s i)))
  (hbound0 :
    ∀ (s : Nat),
      @LT.lt.{0} Nat instLTNat s M → ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (w0 s i) U)
  (hbound1 :
    ∀ (s : Nat),
      @LT.lt.{0} Nat instLTNat s M → ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (w1 s i) U)
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
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt occ)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maps)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt coeff0)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt coeff1)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masks)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rawLeft)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rawRight)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work) (@List.nil.{0} Int)))))))))))))
    μ (ThreeSum.LightBlockSourceHashes.time J L n) fun (x : Int) (ν : Nat → Int) =>
    And
      (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i n →
          @Eq.{1} Int (ν (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawLeft i))
            (@Nat.cast.{0} Int instNatCastInt
              (ThreeSum.OneHotMask.eval (ThreeSum.BlockCoefficientRows.flat J L p sel w0)
                (ThreeSum.BlockCoefficientRows.flat J L p sel w1)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L) (mask i))))
      (And
        (∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i n →
            @Eq.{1} Int (ν (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawRight i))
              (@Nat.cast.{0} Int instNatCastInt
                (ThreeSum.OneHotMask.eval (ThreeSum.BlockCoefficientRows.flat J L p sel w1)
                  (ThreeSum.BlockCoefficientRows.flat J L p sel w0)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L) (mask i))))
        (And (ThreeSum.LightBlockCoefficients.Rows ν coeff0 coeff1 L p sel w0 w1 J) (Light.Kept μ ν coeff0))) := by
  sorry
