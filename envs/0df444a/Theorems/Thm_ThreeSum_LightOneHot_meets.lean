-- Prove2me | Theorems.Thm_ThreeSum_LightOneHot_meets
-- name    : ThreeSum.LightOneHot.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:50:50.774572+00:00
-- url     : https://prove2.me/theorems/e6b38f5a-5221-4fb6-a718-94dd11270814
-- title:
--   The executable one-hot evaluator returns the selected coefficient sum
-- statement:
--   Let a program contain the recursive one-hot evaluator at procedure $p_H$. Let its space, word, and depth limits be $S,M,D$. Memory $\mu$ stores $2^j$ at $u+j$ for $j\le W$, and stores natural coefficients $w_0(j),w_1(j)\le U$ at $v_0+j,v_1+j$ for $j<W$. Assume
--   $$S\le M,\quad u+W+1\le S,\quad v_0+W,v_1+W\le S,\quad 2^{W+1}+(W+1)U\le M.$$
--   For natural numbers $L,m,d$ with $L\le W$, $m<2^L$, and $d+L\le D$, calling $p_H$ with $(L,m,W,u,v_0,v_1)$ succeeds within $100L+30$ steps and returns
--   $$r=\sum_{j=0}^{L-1}w_{\operatorname{bit}_j(m)}(j),\qquad \mu'=\mu.$$
--   Here $\operatorname{bit}_j(m)$ is the $j$th binary digit.
--
--   This certifies the coefficient evaluation used to compute the one-hot encoding hashes.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightOneHot.lean#L38-L125

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
import Theorems.Thm_ThreeSum_OneHotMask_eval_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.OneHotMask
end ThreeSum.OneHotMask

theorem ThreeSum.LightOneHot.meets : ∀ {lim : Light.Limits} {P : Light.Program} {pHash W powers src0 src1 U : Nat}
  (hprog :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pHash)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightOneHot.body pHash)))
  (μ : Nat → Int) (w0 w1 : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) powers
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      lim.space)
  (hsrc0 : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src0 W) lim.space)
  (hsrc1 : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src1 W) lim.space)
  (hword : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightOneHot.word W U)) lim.word)
  (hpowers : ThreeSum.LightSubsetAddress.Powers μ powers W)
  (hread0 :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i W →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src0 i))
          (@Nat.cast.{0} Int instNatCastInt (w0 i)))
  (hread1 :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i W →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src1 i))
          (@Nat.cast.{0} Int instNatCastInt (w1 i)))
  (hbound0 : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i W → @LE.le.{0} Nat instLENat (w0 i) U)
  (hbound1 : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i W → @LE.le.{0} Nat instLENat (w1 i) U) (L m : Nat),
  @LE.le.{0} Nat instLENat L W →
    @LT.lt.{0} Nat instLTNat m
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L) →
      ∀ (d : Nat),
        @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L) lim.depth →
          Light.Meets lim P pHash d
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt m)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt W)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt powers)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src0)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src1) (@List.nil.{0} Int)))))))
            μ (ThreeSum.LightOneHot.time L) fun (r : Int) (μ' : Nat → Int) =>
            And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.OneHotMask.eval w0 w1 L m)))
              (@Eq.{1} (Nat → Int) μ' μ) := by
  sorry
