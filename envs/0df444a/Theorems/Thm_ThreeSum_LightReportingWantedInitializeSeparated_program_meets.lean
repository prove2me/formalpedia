-- Prove2me | Theorems.Thm_ThreeSum_LightReportingWantedInitializeSeparated_program_meets
-- name    : ThreeSum.LightReportingWantedInitializeSeparated.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T17:23:34.596509+00:00
-- url     : https://prove2.me/theorems/e5e7eaef-b0a1-4eff-aaf1-01ab51362c7b
-- title:
--   Initialize a wanted frontier while updating its retained dense counter
-- statement:
--   Let $A,B,C$ be finite sets with integer value maps, and let $w$ select a source index in $A$, a signed lift, and a global output. Assume its lifted source residue agrees with that output key modulo the global encoding modulus. Let $I$ be the resulting raw incidence set, $m$ the root-prefix mass for $w$, and $G=\binom{2h}{h}$.
--
--   Suppose memory stores the exact source stages, level-zero catalog and metadata, raw output rows, group size, old count $o$, and threshold $\theta$. The counter precedes the raw and packed rows; catalog bounds, query scratch, packing space, and frontier capacity satisfy the stated layout contracts. Require $S\le W$, $o+m+\theta+2\le W$, and $d+2(512hJ)+16\le D$. Execution returns
--   $$r=\mathbf1_{\theta<o+m},\qquad\nu(\mathrm{counter})=o+m,$$
--   and stores the exact root frontier, root mass $m$, capacity $(m+1)G$, and packed output masks. It meets the initialization budget and preserves memory below the packed rows except the counter.
--
--   This initializes one wanted search without losing the retained running state.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedInitializeSeparated.lean#L27-L116

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
import Theorems.Thm_ThreeSum_LightBlockMasks_meets
import Theorems.Thm_ThreeSum_LightReportingInitializeStored_program_meets
import Theorems.Thm_ThreeSum_ReportingHostLevelData_Stored_of_kept
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt


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
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
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
namespace ThreeSum.LightReportingWantedInitialize
end ThreeSum.LightReportingWantedInitialize
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
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

universe u_1 u_2 u_3

theorem ThreeSum.LightReportingWantedInitializeSeparated.program_meets : ∀ {lim : Light.Limits} {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β]
  [Fintype.{u_3} γ] [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {μ : Nat → Int}
  {h J baseL baseR catalogs cover rawRows rows counter root maskBase work old threshold d : Nat}
  {D : ThreeSum.ReportingHostLevelData.Catalog} (pMod shift : Int) (A : Finset.{u_1} α) (B : Finset.{u_2} β)
  (C : Finset.{u_3} γ) (a : α → Int) (b : β → Int) (c : γ → Int) (w : ThreeSum.RawReporting.Wanted.{u_1} h J α)
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
      baseR rows)
  (HW :
    ThreeSum.ReportingHostLevelData.Scratch lim h J (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D
      (@Finset.card.{u_2} β B) (@Finset.card.{u_3} γ C) maskBase work)
  (hmeta : Light.SegN μ catalogs (D.record h (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (hmetaEnd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) catalogs
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
      rows)
  (hgroup :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cover
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.groupSize h)))
  (hcoverEnd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cover
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      rows)
  (hraw : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawRows J) rows)
  (hrows : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rows J) root)
  (hcounter :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      rawRows)
  (hout :
    @LE.le.{0} Nat instLENat
      (ThreeSum.ReportingHostFrontierLayout.slot root
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
  (hpackSpace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
              (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst h J
                (@ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
                  (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
                    (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
                    (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
                    (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
                    (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
                      (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
                  a b c)
                w))
            threshold)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      lim.word)
  (hreadRaw :
    Light.SegN μ rawRows
      (@ThreeSum.BlockMaskLayout.rawMasks J
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
        (@ThreeSum.BlockForced.outputRows h J
          (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J)
            (@Prod.snd.{u_1, 0} α
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w)))))
  (hcounterRead : @Eq.{1} Int (μ counter) (@Nat.cast.{0} Int instNatCastInt old))
  (hthreshold :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Nat.cast.{0} Int instNatCastInt threshold))
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (ThreeSum.LightBlockQuery.width h J)))
        (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
      lim.depth),
  Light.Meets lim ThreeSum.LightReportingWantedInitialize.program
    (@OfNat.ofNat.{0} Nat (nat_lit 41) (instOfNatNat (nat_lit 41))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockQuery.width h J))
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockQuery.sourceCut h J))
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
          (@List.cons.{0} Int
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512))) (@Nat.cast.{0} Int instNatCastInt h))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseL)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseR)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt catalogs)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rawRows)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rows)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cover)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt counter)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt root)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maskBase)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                (@List.nil.{0} Int)))))))))))))))
    μ (ThreeSum.LightReportingWantedInitialize.time h J D.t) fun (result : Int) (ν : Nat → Int) =>
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
      (@Eq.{1} Int result
        (@ite.{1} Int
          (@LT.lt.{0} Nat instLTNat threshold
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
              (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst h J I w)))
          (threshold.decLt
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
              (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst h J I w)))
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (And
        (@Eq.{1} Int (ν counter)
          (@Nat.cast.{0} Int instNatCastInt
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
              (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst h J I w))))
        (And
          (@ThreeSum.ReportingHostFrontierLayout.At.{u_1, u_2, u_3} α β γ inst h J ν I w root
            (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β γ inst h J I w)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (And
            (@Eq.{1} Int
              (ν
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) root
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@Nat.cast.{0} Int instNatCastInt
                (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst h J I w)))
            (And
              (@Eq.{1} Int
                (ν
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) root
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@Nat.cast.{0} Int instNatCastInt
                  (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β γ inst h J I w)))
              (And
                (Light.SegN ν rows
                  (@ThreeSum.BlockMaskLayout.packedMasks J
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                    (@ThreeSum.BlockForced.outputRows h J
                      (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (ThreeSum.GlobalEncoding.GlobalOutput h J)
                        (@Prod.snd.{u_1, 0} α
                          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (ThreeSum.GlobalEncoding.GlobalOutput h J))
                          w)))))
                (Light.KeptBut μ ν rows counter (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) := by
  sorry
