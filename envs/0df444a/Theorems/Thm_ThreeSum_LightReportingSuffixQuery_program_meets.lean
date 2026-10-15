-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixQuery_program_meets
-- name    : ThreeSum.LightReportingSuffixQuery.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:48:02.728527+00:00
-- url     : https://prove2.me/theorems/4c5eaa87-d3d2-453c-823a-6969a1d19e33
-- title:
--   Evaluate a suffix Möbius query from explicit layers and canonical boxes
-- statement:
--   Embed $[V]$ into $[W]$ by a coordinate shift $\iota$. Let $Q\subseteq[V]$, $s,c\le W$, $t\le|Q|+1$, and $|Q|-t\le b\le|Q|$. Prefixes $P_L,P_R$ are disjoint from $\iota Q$, and their unions with it have size at most $c$. Suppose $f,g$ have bounds $B,D$ on this downset, all suffix stages are retained, and all prefix box stages of $\lambda(S)=(-1)^{|S|}Z_sf(P_L\cup\iota S)Z_sg(P_R\cup\iota S)$ are stored through width $V$ with cutoff $b$. Under the prescribed separated tables, query-mask capacity, scratch, control and sparse-query magnitude bounds, space fitting in a word, and depth $d+W+9$, the program returns
--   $$
--   \sum_{T\subseteq\iota Q}(-1)^{|Q|-|T|}Z_sf(P_L\cup T)Z_sg(P_R\cup T).
--   $$
--   It meets the suffix-query time budget; below scratch only the query-mask buffer may change.
--
--   This computes the required Möbius value using the explicit/box partition.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSuffixQuery.lean#L90-L200

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
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
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
import Mathlib.Data.List.Sublists
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
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_meets
import Theorems.Thm_ThreeSum_LightReportingSuffixExplicit_meets
import Theorems.Thm_ThreeSum_LightSign_meets
import Theorems.Thm_ThreeSum_SparseBoxes_mem_explicitLeaves
import Theorems.Thm_ThreeSum_SparseBoxes_sparse_query_identity
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_abs_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.LightReportingSuffixQuery.program_meets : ∀ {lim : Light.Limits} {μ : Nat → Int} {W V offset cut stage t baseL baseR boxCut boxBase maskBase work B D d : Nat}
  (hfit : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset V) W)
  (Q : Finset.{0} (Fin V)) (preL preR : Finset.{0} (Fin W)) (f g : Finset.{0} (Fin W) → Int)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hcut : @LE.le.{0} Nat instLENat cut W) (hstage : @LE.le.{0} Nat instLENat stage W)
  (hdataL :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) baseL
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (ThreeSum.SubsetAddress.downsetCap W cut)))
      maskBase)
  (hdataR :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) baseR
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (ThreeSum.SubsetAddress.downsetCap W cut)))
      maskBase)
  (hdataBox :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) boxBase
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) V
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (ThreeSum.SubsetAddress.downsetCap V boxCut)))
      maskBase)
  (hmasks :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maskBase
        (ThreeSum.LightSparseQuery.queryItems (@Finset.card.{0} (Fin V) Q) t))
      work)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (ThreeSum.LightPascal.tableSize W))
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
  (hvalueWord :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (ThreeSum.LightSparseQuery.magnitudeBound V stage (@Finset.card.{0} (Fin V) Q) t B D))
      lim.word)
  (ht :
    @LE.le.{0} Nat instLENat t
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{0} (Fin V) Q)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hboxCut : @LE.le.{0} Nat instLENat boxCut (@Finset.card.{0} (Fin V) Q))
  (hflags :
    @LE.le.{0} Nat instLENat
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Finset.card.{0} (Fin V) Q) t) boxCut)
  (hdisjL :
    @Disjoint.{0} (Finset.{0} (Fin W)) (@Finset.instPartialOrder.{0} (Fin W)) (@Finset.instOrderBot.{0} (Fin W)) preL
      (@ThreeSum.ReportingHostSuffix.liftSet W V offset hfit Q))
  (hdisjR :
    @Disjoint.{0} (Finset.{0} (Fin W)) (@Finset.instPartialOrder.{0} (Fin W)) (@Finset.instOrderBot.{0} (Fin W)) preR
      (@ThreeSum.ReportingHostSuffix.liftSet W V offset hfit Q))
  (hcardL :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} (Fin W)
        (@Union.union.{0} (Finset.{0} (Fin W)) (@Finset.instUnion.{0} (Fin W) (instDecidableEqFin W)) preL
          (@ThreeSum.ReportingHostSuffix.liftSet W V offset hfit Q)))
      cut)
  (hcardR :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} (Fin W)
        (@Union.union.{0} (Finset.{0} (Fin W)) (@Finset.instUnion.{0} (Fin W) (instDecidableEqFin W)) preR
          (@ThreeSum.ReportingHostSuffix.liftSet W V offset hfit Q)))
      cut)
  (hf :
    ∀ (T : Finset.{0} (Fin W)),
      @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin W) T) cut →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (f T))
          (@Nat.cast.{0} Int instNatCastInt B))
  (hg :
    ∀ (T : Finset.{0} (Fin W)),
      @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin W) T) cut →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (g T))
          (@Nat.cast.{0} Int instNatCastInt D))
  (hstoredL : @ThreeSum.LightZetaStages.StoredThrough W μ baseL cut f W)
  (hstoredR : @ThreeSum.LightZetaStages.StoredThrough W μ baseR cut g W)
  (hstoredBox :
    @ThreeSum.LightBoxStages.StoredThrough V μ boxBase boxCut
      (@ThreeSum.ReportingHostSuffix.leafWeight W V offset hfit f g stage preL preR) V)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d W)
        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
      lim.depth),
  Light.Meets lim ThreeSum.LightReportingSuffixQuery.program
    (@OfNat.ofNat.{0} Nat (nat_lit 28) (instOfNatNat (nat_lit 28))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt W)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt stage)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@Finset.card.{0} (Fin W) preL))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@ThreeSum.SubsetAddress.subsetMask W preL))
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@Finset.card.{0} (Fin W) preR))
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@ThreeSum.SubsetAddress.subsetMask W preR))
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt V)
                    (@List.cons.{0} Int
                      (@HPow.hPow.{0, 0, 0} Int Nat Int
                        (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) offset)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@Finset.card.{0} (Fin V) Q))
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@ThreeSum.SubsetAddress.subsetMask V Q))
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt t)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseL)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseR)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt boxCut)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt boxBase)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maskBase)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                        (@List.nil.{0} Int)))))))))))))))))))
    μ (ThreeSum.LightReportingSuffixQuery.time W V (@Finset.card.{0} (Fin V) Q) t) fun (r : Int) (μ' : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@ThreeSum.Subset.mobius.{0} (Fin W)
          (fun (S : Finset.{0} (Fin W)) =>
            @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (@ThreeSum.SubsetStages.stageValue W f stage
                (@Union.union.{0} (Finset.{0} (Fin W)) (@Finset.instUnion.{0} (Fin W) (instDecidableEqFin W)) preL S))
              (@ThreeSum.SubsetStages.stageValue W g stage
                (@Union.union.{0} (Finset.{0} (Fin W)) (@Finset.instUnion.{0} (Fin W) (instDecidableEqFin W)) preR S)))
          (@ThreeSum.ReportingHostSuffix.liftSet W V offset hfit Q)))
      (Light.KeptBut μ μ' work maskBase (ThreeSum.LightSparseQuery.queryItems (@Finset.card.{0} (Fin V) Q) t)) := by
  sorry
