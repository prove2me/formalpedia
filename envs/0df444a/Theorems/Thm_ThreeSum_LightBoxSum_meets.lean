-- Prove2me | Theorems.Thm_ThreeSum_LightBoxSum_meets
-- name    : ThreeSum.LightBoxSum.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:40:42.981026+00:00
-- url     : https://prove2.me/theorems/a2dff03f-4709-4b4d-b94d-8b7b0fba3eec
-- title:
--   Sum an explicit list of canonical sparse boxes
-- statement:
--   Let $Q\subseteq[L]$, cutoff $c\le L$, and integer weights $w(T)$ satisfy $|w(T)|\le B$ whenever $|T|\le c$. A stored list $\mathcal U$ consists of subsets $U\subseteq Q$ with $|U|=t$ and $|Q\setminus U|\le c$. Memory contains their masks and every compact prefix-zeta stage of $w$, all below scratch $f$. Set $D_c=\sum_{j=0}^{c}\binom Lj$; the stage area has $(L+1)D_c$ cells.
--
--   Assume the specified box-query procedures, $f+(L+1)^2+L+1\le S\le W$, $(L+1)2^{L+1},|\mathcal U|2^LB\le W$, and $d+L+7\le D$. With $F_U=Q\setminus U$ and $E_U=\{x\in F_U:x<y\ \forall y\in U\}$, the return value is
--   $$r=\sum_{U\in\mathcal U}\ \sum_{F_U\setminus E_U\subseteq T\subseteq F_U}w(T),$$
--   counting list repetitions. Time is $|\mathcal U|(T_{\rm box}(L)+60)+40$, and memory below $f$ is preserved.
--
--   This executes the explicit box part of a sparse query.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBoxSum.lean#L59-L150

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
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
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_ThreeSum_BoxBounds_boxSum_abs_le
import Theorems.Thm_ThreeSum_LightQueryBox_meets
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightBoxSum.meets : ∀ {lim : Light.Limits} {P : Light.Program}
  {pMain pBox pMinimum pLookup pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightBoxSum.body pBox)))
  (hBox :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pBox)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightQueryBox.body pMinimum pLookup)))
  (hMinimum :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMinimum)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightMaskMinimum.body pPowers pErase)))
  (hLookup :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pLookup)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightStageLookup.body pSize pAddress)))
  (hSize :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pSize)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightDownsetSize.body pSetup pOffset)))
  (hAddress :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pAddress)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightDownsetAddress.body pSetup pOffset)))
  (C : ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
  (hOffset :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pOffset)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSubsetOffset.body))
  (hErase :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pErase)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightMaskErase.body pErase)))
  {μ : Nat → Int} {L cut t maskBase base work B d : Nat} (Q : Finset.{0} (Fin L))
  (missing : List.{0} (Finset.{0} (Fin L))) (weight : Finset.{0} (Fin L) → Int)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hcut : @LE.le.{0} Nat instLENat cut L)
  (hdata :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (ThreeSum.SubsetAddress.downsetCap L cut)))
      work)
  (hmasks :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maskBase
        (@List.length.{0} (Finset.{0} (Fin L)) missing))
      work)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work (ThreeSum.LightPascal.tableSize L))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
      lim.word)
  (haccWord :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@List.length.{0} (Finset.{0} (Fin L)) missing)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
            B)))
      lim.word)
  (hvalid :
    ∀ (U : Finset.{0} (Fin L)),
      @Membership.mem.{0, 0} (Finset.{0} (Fin L)) (List.{0} (Finset.{0} (Fin L)))
          (@List.instMembership.{0} (Finset.{0} (Fin L))) missing U →
        And
          (@LE.le.{0} (Finset.{0} (Fin L))
            (@Preorder.toLE.{0} (Finset.{0} (Fin L))
              (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin L)) (@Finset.instPartialOrder.{0} (Fin L))))
            U Q)
          (And (@Eq.{1} Nat (@Finset.card.{0} (Fin L) U) t)
            (@LE.le.{0} Nat instLENat
              (@Finset.card.{0} (Fin L)
                (@SDiff.sdiff.{0} (Finset.{0} (Fin L)) (@Finset.instSDiff.{0} (Fin L) (instDecidableEqFin L)) Q U))
              cut)))
  (hweight :
    ∀ (S : Finset.{0} (Fin L)),
      @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) S) cut →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (weight S))
          (@Nat.cast.{0} Int instNatCastInt B))
  (hstored : @ThreeSum.LightBoxStages.StoredThrough L μ base cut weight L)
  (hseg :
    Light.SegN μ maskBase (@List.map.{0, 0} (Finset.{0} (Fin L)) Nat (@ThreeSum.SubsetAddress.subsetMask L) missing))
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L)
        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
      lim.depth),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@Finset.card.{0} (Fin L) Q))
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@ThreeSum.SubsetAddress.subsetMask L Q))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt t)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} (Finset.{0} (Fin L)) missing))
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maskBase)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work) (@List.nil.{0} Int))))))))))
    μ (ThreeSum.LightBoxSum.time L (@List.length.{0} (Finset.{0} (Fin L)) missing)) fun (r : Int) (μ' : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@List.sum.{0} Int Int.instAdd
          (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))
          (@List.map.{0, 0} (Finset.{0} (Fin L)) Int (@ThreeSum.LightBoxSum.boxValue L Q weight) missing)))
      (Light.Kept μ μ' work) := by
  sorry
