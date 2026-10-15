-- Prove2me | Theorems.Thm_ThreeSum_LightReportingInitialize_program_meets
-- name    : ThreeSum.LightReportingInitialize.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T17:14:55.786277+00:00
-- url     : https://prove2.me/theorems/dd6715d4-d7c9-4cb1-b96a-227d120ad635
-- title:
--   Initializing the reporting frontier from the exact root mass
-- statement:
--   Write $S,\Omega,\Delta$ for machine space, word magnitude, and depth limits. Let finite labeled integer inputs $A,B,C$, with maps $a,b,c$, induce raw representations $I$ at integer parameters $p,\delta$. Fix a wanted label $w=(x,\ell,q)$, where $\ell\in\{-1,0,1\}$, with $x\in A$ and the global key congruence $M\mid a(x)\bmod p+\ell p+\delta-\operatorname{key}(q)$. Define
--   $$m=\#\{u\in I:\operatorname{wanted}(u)=w\},\qquad
--   G=\binom{2h}h,\qquad C_0=(m+1)G.$$
--   Assume exact source transforms and a complete level-zero catalog. Its retained regions end before root $o$; the catalog scratch predicate holds, $o+4+2C_0$ precedes the query masks, $S\le\Omega$, and $d+1024hJ+13\le\Delta$. Here $M$ is the global block modulus.
--
--   The initializer returns $\mathbf1_{m>0}$ and stores the exact level-zero frontier
--   $$\mathcal F_0=\begin{cases}[\,[]\,],&m>0,\\[],&m=0,\end{cases}
--   \qquad \nu(o+2)=m,\quad \nu(o+3)=C_0.$$
--   The frontier record includes its count, full query mask, and the empty left/right prefix masks when present. It preserves cells below $o$ and uses the level-zero catalog-query time plus $400$.
--
--   This starts reporting with precisely the live root prefix and its allocated capacity.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingInitialize.lean#L45-L152

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
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
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
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
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
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
import Theorems.Thm_ThreeSum_LightReportingCatalogQuery_program_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
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
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSumApsp
end ThreeSumApsp

universe u_1 u_2 u_3

theorem ThreeSum.LightReportingInitialize.program_meets : ∀ {lim : Light.Limits} {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β]
  [Fintype.{u_3} γ] [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {μ : Nat → Int}
  {h J baseL baseR maskBase work dst depth : Nat} {D : ThreeSum.ReportingHostLevelData.Catalog} (pMod shift : Int)
  (A : Finset.{u_1} α) (B : Finset.{u_2} β) (C : Finset.{u_3} γ) (a : α → Int) (b : β → Int) (c : γ → Int)
  (w : ThreeSum.RawReporting.Wanted.{u_1} h J α)
  (hkey :
    And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) A
        (@Prod.fst.{u_1, 0} α
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J))
          w))
      (@Dvd.dvd.{0} Int Int.instDvd (ThreeSum.GlobalEncoding.globalModulus h J)
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
              (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
                (a
                  (@Prod.fst.{u_1, 0} α
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput h J))
                    w))
                pMod)
              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                (ThreeSum.RawIncidences.lift
                  (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (ThreeSum.GlobalEncoding.GlobalOutput h J)
                    (@Prod.snd.{u_1, 0} α
                      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (ThreeSum.GlobalEncoding.GlobalOutput h J))
                      w)))
                pMod))
            shift)
          (@ThreeSum.GlobalEncoding.globalKey h J
            (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput h J)
              (@Prod.snd.{u_1, 0} α
                (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput h J))
                w))))))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (HS :
    @ThreeSum.ReportingHostLevelData.Sources.{u_2, u_3} β γ h J μ pMod shift B C b c
      (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (ThreeSum.GlobalEncoding.GlobalOutput h J)
        (@Prod.snd.{u_1, 0} α
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J))
          w))
      baseL baseR)
  (HC :
    @ThreeSum.ReportingHostLevelData.Stored.{u_2, u_3} β γ h J
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) μ D (Nat.zero_le J) pMod shift B C b c
      (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (ThreeSum.GlobalEncoding.GlobalOutput h J)
        (@Prod.snd.{u_1, 0} α
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J))
          w)))
  (HB :
    ThreeSum.ReportingHostLevelData.Bounds h J (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D baseL
      baseR dst)
  (HW :
    ThreeSum.ReportingHostLevelData.Scratch lim h J (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D
      (@Finset.card.{u_2} β B) (@Finset.card.{u_3} γ C) maskBase work)
  (hout :
    @LE.le.{0} Nat instLENat
      (ThreeSum.ReportingHostFrontierLayout.slot dst
        (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β γ inst h J
          (@ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
            (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
              (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
              (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
              (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
              (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
                (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
            a b c)
          w)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      maskBase)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (ThreeSum.LightBlockQuery.width h J)))
        (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))
      lim.depth),
  Light.Meets lim ThreeSum.LightReportingInitialize.program
    (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))) depth
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockQuery.width h J))
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockQuery.sourceCut h J))
        (@List.cons.{0} Int
          (@Nat.cast.{0} Int instNatCastInt
            (ThreeSum.BlockIndexedQuery.suffixStage J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons.{0} Int
                    (@Nat.cast.{0} Int instNatCastInt
                      (ThreeSum.BlockIndexedQuery.suffixStage J
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                    (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons.{0} Int
                        (@Nat.cast.{0} Int instNatCastInt
                          (ThreeSum.LightBlockQuery.residualSize h J
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                        (@List.cons.{0} Int
                          (@Nat.cast.{0} Int instNatCastInt
                            (@ThreeSum.SubsetAddress.subsetMask
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                              (@ThreeSum.BlockIndexedQuery.querySet J
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                (@ThreeSum.BlockForced.outputRows h J
                                  (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                    (ThreeSum.GlobalEncoding.GlobalOutput h J)
                                    (@Prod.snd.{u_1, 0} α
                                      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                        (ThreeSum.GlobalEncoding.GlobalOutput h J))
                                      w))))))
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt D.t)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseL)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseR)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt D.boxCut)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt D.indexBase)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt D.ptrBase)
                                      (@List.cons.{0} Int
                                        (@Nat.cast.{0} Int instNatCastInt
                                          (ThreeSum.LightReportingPrefixCatalog.count h
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maskBase)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                                              (@List.cons.{0} Int
                                                (@Nat.cast.{0} Int instNatCastInt
                                                  (ThreeSum.LocalCoverBounds.groupSize h))
                                                (@List.nil.{0} Int)))))))))))))))))))))))
    μ (ThreeSum.LightReportingInitialize.time h J D.t) fun (r : Int) (ν : Nat → Int) =>
    have I :=
      @ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
        (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
          (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
          (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
          (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
          (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
            (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
        a b c;
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt
          (@List.length.{0}
            (List.{0}
              (Finset.{0}
                (Fin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
            (@ThreeSum.ReportingHostFrontier.frontier.{u_1, u_2, u_3} α β γ inst h J I w
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (And
        (@ThreeSum.ReportingHostFrontierLayout.At.{u_1, u_2, u_3} α β γ inst h J ν I w dst
          (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β γ inst h J I w)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (And
          (@Eq.{1} Int
            (ν
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@Nat.cast.{0} Int instNatCastInt
              (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst h J I w)))
          (And
            (@Eq.{1} Int
              (ν
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              (@Nat.cast.{0} Int instNatCastInt
                (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β γ inst h J I w)))
            (Light.Kept μ ν dst)))) := by
  sorry
