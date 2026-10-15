-- Prove2me | Theorems.Thm_ThreeSum_LightQueryEnumeration_meets
-- name    : ThreeSum.LightQueryEnumeration.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:48:43.458812+00:00
-- url     : https://prove2.me/theorems/d1cab46b-982a-4e2f-b228-64b985ce83ba
-- title:
--   Enumerating fixed-size subsets inside an arbitrary query mask
-- statement:
--   Let $Q\subseteq\{0,\ldots,W-1\}$ have size $c$, and let $t\le c+1$. For a destination $a$ and scratch base $w$, assume
--   $$a+\binom ct\le w,\quad w+2W+2\le S\le B,\quad2^{W+1}\le B,\quad d+W+2\le D.$$
--   With the specified weight builder, powers, erasure, and recursive subset procedures, the call returns $\binom ct$ and writes the masks of exactly the $t$-element subsets of $Q$, in the defined recursive enumeration order. It also retains at $w$ the weights $2^{q_0},\ldots,2^{q_{c-1}}$, for the increasing coordinates of $Q$. Its budget is
--   $$100W^2+147W+185+150\mathcal E(c,t),$$
--   where $\mathcal E$ is the defined recursive enumeration-work count, including recursive calls and emitted-list lengths. Cells below $w$ outside the destination are preserved.
--
--   This enumerates query subsets using only the compact coordinate set, with the zero-output case $t=c+1$ included.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightQueryEnumeration.lean#L26-L71

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
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
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
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
import Theorems.Thm_ThreeSum_LightQueryWeights_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_meets
import Theorems.Thm_ThreeSum_QueryCoordinates_output_missingSets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightQueryEnumeration.meets : ∀ {lim : Light.Limits} {P : Light.Program} {pMain pWeights pPowers pErase pEnum : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightQueryEnumeration.body pWeights pEnum)))
  (hweights :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pWeights)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightQueryWeights.body pPowers pErase)))
  (hpowers :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pPowers)
      (@Option.some.{0} Light.Stmt Light.powTableBody))
  (herase :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pErase)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightMaskErase.body pErase)))
  (henum :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pEnum)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightSubsetEnumeration.body pEnum)))
  {μ : Nat → Int} {W t dst work d : Nat} (Q : Finset.{0} (Fin W))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      lim.word)
  (ht :
    @LE.le.{0} Nat instLENat t
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{0} (Fin W) Q)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hdst :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst ((@Finset.card.{0} (Fin W) Q).choose t))
      work)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d W)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      lim.depth),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt W)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@ThreeSum.SubsetAddress.subsetMask W Q))
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt t)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work) (@List.nil.{0} Int))))))
    μ (ThreeSum.LightQueryEnumeration.time W (@Finset.card.{0} (Fin W) Q) t) fun (r : Int) (μ' : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt ((@Finset.card.{0} (Fin W) Q).choose t)))
      (And
        (Light.SegN μ' dst
          (@List.map.{0, 0} (Finset.{0} (Fin W)) Nat (@ThreeSum.SubsetAddress.subsetMask W)
            (@ThreeSum.QueryCoordinates.missingSets W Q t)))
        (And
          (ThreeSum.LightWeightedEnumeration.Weights μ' work (@Finset.card.{0} (Fin W) Q)
            (@ThreeSum.QueryCoordinates.weights W Q))
          (Light.KeptBut μ μ' work dst ((@Finset.card.{0} (Fin W) Q).choose t)))) := by
  sorry
