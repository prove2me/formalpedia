-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_join_ends
-- name    : ThreeSum.LightKaratsuba.join_ends
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:45:29.993065+00:00
-- url     : https://prove2.me/theorems/0d050c24-fa4c-45bf-a9e3-e69795c9087d
-- title:
--   Correct recombination of three Karatsuba work arrays
-- statement:
--   Let $n=2h>0$. Initial memory contains integer arrays $u,v,z$ of length $n$ at $w,w+n,w+2n$, with every entry of absolute value at most $U$. Assume the specified linear-combination and fill procedures are available. For machine limits $S,B,D$, require
--   $$o+2n\le w,\quad w+3n\le S\le B,\quad10U\le B,\quad d<D.$$
--   Execute the join body from its specified frame, with arbitrary unused source pointers and prior return value. Within $200n+300$ steps, its final memory satisfies
--   $$\nu(o+j)=\widetilde u(j)+\widetilde{(z-u-v)}(j-h)+\widetilde v(j-n)\qquad(0\le j<2n),$$
--   where each tilde denotes zero extension outside indices $0,\ldots,n-1$. Cells below $w$ outside $[o,o+2n)$ are preserved.
--
--   This establishes the array recombination step; the inputs need only satisfy the stated bounds, independently of how the three arrays were obtained.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightKaratsuba.lean#L143-L272

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
import Theorems.Thm_Light_Ends_pass
import Theorems.Thm_ThreeSum_LightArray_linear_bounded_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba

theorem ThreeSum.LightKaratsuba.join_ends : ∀ {lim : Light.Limits} {P : Light.Program} {d pLinear pFill : Nat}
  (hLinear :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pLinear)
      (@Option.some.{0} Light.Stmt ThreeSum.LightArray.linearBody))
  (hFill :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pFill)
      (@Option.some.{0} Light.Stmt Light.fillBody))
  {μ : Nat → Int} {n half a b out work U : Nat} {r : Int}
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  (hhalf :
    @Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) half)
      n)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hout :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) out
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      work)
  (hwork :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
        (@OfNat.ofNat.{0} Int (nat_lit 10) (@instOfNat (nat_lit 10))) (@Nat.cast.{0} Int instNatCastInt U))
      lim.word)
  (hvalues :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        And
          (@LE.le.{0} Int Int.instLEInt
            (@abs.{0} Int instLatticeInt Int.instAddGroup
              (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work i)))
            (@Nat.cast.{0} Int instNatCastInt U))
          (And
            (@LE.le.{0} Int Int.instLEInt
              (@abs.{0} Int instLatticeInt Int.instAddGroup
                (μ
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work n) i)))
              (@Nat.cast.{0} Int instNatCastInt U))
            (@LE.le.{0} Int Int.instLEInt
              (@abs.{0} Int instLatticeInt Int.instAddGroup
                (μ
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                    i)))
              (@Nat.cast.{0} Int instNatCastInt U))))
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth),
  Light.Ends lim P d (ThreeSum.LightKaratsuba.joinBody pLinear pFill)
    {
      loc :=
        Light.frame
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt out)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt half)
                      (@List.cons.{0} Int r (@List.nil.{0} Int)))))))),
      mem := μ }
    (ThreeSum.LightKaratsuba.joinTime n) fun (σ' : Light.State) =>
    And
      (∀ (j : Nat),
        @LT.lt.{0} Nat instLTNat j
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n) →
          @Eq.{1} Int (σ'.mem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) out j))
            (ThreeSum.LightKaratsuba.joined μ work n half j))
      (Light.KeptBut μ σ'.mem work out
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)) := by
  sorry
