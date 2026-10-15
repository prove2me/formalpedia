-- Prove2me | Theorems.Thm_ThreeSum_LightCanonicalBoxSum_meets
-- name    : ThreeSum.LightCanonicalBoxSum.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:44:13.239823+00:00
-- url     : https://prove2.me/theorems/fbc26d5f-cb79-4d8a-a77d-248b6d6d5d7e
-- title:
--   Sum all canonical boxes at a fixed missing-set layer
-- statement:
--   Let $Q\subseteq[W]$, $t\le|Q|+1$, and $|Q|-t\le c\le W$. Let integer weights satisfy $|w(S)|\le B$ for $|S|\le c$, and suppose every prefix zeta stage of $w$ on that downset is stored. For $U\subseteq Q$, let $F_U=\{x\in Q\setminus U:x<y\text{ for every }y\in U\}$. With the tables ending before a $\binom{|Q|}{t}$-cell mask buffer and sufficient ranking scratch, assume space fits in a word, the control and $\binom{|Q|}{t}2^WB$ word bounds, and depth $d+W+8$. The installed routine returns
--   $$
--   \sum_{\substack{U\subseteq Q\\|U|=t}}\ \sum_{Q\setminus(U\cup F_U)\subseteq S\subseteq Q\setminus U}w(S).
--   $$
--   Its time is the fixed-cardinality query enumeration cost plus the box-sum batch cost and $50$ steps. Below scratch, only the mask buffer may change.
--
--   This evaluates the canonical-box part of a sparse subset query.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightCanonicalBoxSum.lean#L59-L115

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
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
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_LightBoxSum_meets
import Theorems.Thm_ThreeSum_LightQueryEnumeration_meets
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
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.LightCanonicalBoxSum.meets : ∀ {lim : Light.Limits} {P : Light.Program} {pMain pEnum pSum : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightCanonicalBoxSum.body pEnum pSum)))
  (C : ThreeSum.LightCanonicalBoxSum.Procs P pEnum pSum) {μ : Nat → Int} {W cut t base maskBase work B d : Nat}
  (Q : Finset.{0} (Fin W)) (weight : Finset.{0} (Fin W) → Int)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hcut : @LE.le.{0} Nat instLENat cut W)
  (hdata :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (ThreeSum.SubsetAddress.downsetCap W cut)))
      maskBase)
  (hmasks :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maskBase ((@Finset.card.{0} (Fin W) Q).choose t))
      work)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work (ThreeSum.LightPascal.tableSize W))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
      lim.word)
  (haccWord :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) ((@Finset.card.{0} (Fin W) Q).choose t)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W)
            B)))
      lim.word)
  (ht :
    @LE.le.{0} Nat instLENat t
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{0} (Fin W) Q)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hflags :
    @LE.le.{0} Nat instLENat
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Finset.card.{0} (Fin W) Q) t) cut)
  (hweight :
    ∀ (S : Finset.{0} (Fin W)),
      @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin W) S) cut →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (weight S))
          (@Nat.cast.{0} Int instNatCastInt B))
  (hstored : @ThreeSum.LightBoxStages.StoredThrough W μ base cut weight W)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d W)
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      lim.depth),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt W)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@Finset.card.{0} (Fin W) Q))
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@ThreeSum.SubsetAddress.subsetMask W Q))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt t)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maskBase)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work) (@List.nil.{0} Int)))))))))
    μ (ThreeSum.LightCanonicalBoxSum.time W (@Finset.card.{0} (Fin W) Q) t) fun (r : Int) (μ' : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (∑ U ∈ @Finset.powersetCard.{0} (Fin W) t Q,
          @ThreeSum.SparseBoxes.boxSum.{0} (Fin W) (@Fin.instLinearOrder W)
            (@SDiff.sdiff.{0} (Finset.{0} (Fin W)) (@Finset.instSDiff.{0} (Fin W) (instDecidableEqFin W)) Q U)
            (@ThreeSum.SparseBoxes.queryFree.{0} (Fin W) (@Fin.instLinearOrder W) Q U) weight))
      (Light.KeptBut μ μ' work maskBase ((@Finset.card.{0} (Fin W) Q).choose t)) := by
  sorry
