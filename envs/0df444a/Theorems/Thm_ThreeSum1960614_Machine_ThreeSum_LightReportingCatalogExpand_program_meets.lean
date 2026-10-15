-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingCatalogExpand_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:37:03.941975+00:00
-- url     : https://prove2.me/theorems/942d3b8b-eeb2-403b-88be-1d10d4b5fd2d
-- title:
--   Complete catalog-backed expansion of a reporting prefix
-- statement:
--   Let finite sets $A,B,C$ carry integer values, let wanted label $w$ satisfy its original membership and exact shifted lifted-key divisibility condition, and let its prefix be valid at depth $k<J$. Suppose both source-stage families, the sorted packed index, exact pointer array, and every next-depth suffix-box table are stored correctly. Let threshold and box cutoff meet the next residual-cardinality conditions. Assume the ordered child-mask, prefix, count, selected-index, and query-scratch buffers fit space; Pascal, power and remainder scratch, lookup and value word bounds, and the stated depth allowance hold. The closed program constructs every actual child and both prefix-mask arrays, stores each exact next-prefix count, filters precisely the selected positive-count children, and returns their number within its stated time. It preserves all input data before the child-mask buffer.
--
--   Connects physical next-block expansion and filtering to the exact original raw-incidence queries. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingCatalogExpand.lean#L41-L170

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Lean
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
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
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
import Mathlib.Data.List.TakeDrop
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_ReportingHostMasks_prefixRows_append
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks


namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
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
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingCatalogExpand
end ThreeSum.LightReportingCatalogExpand
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
end ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.program_meets
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase indexBase ptrBase masks dstL dstR dst selected maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (pre : List (Finset (Fin (464*h)))) (hk : k < J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
      (a w.1 % pMod+_root_.ThreeSum.RawIncidences.lift w.2.1*pMod+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*_root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.LightBlockQuery.sourceCut h J) ≤ masks)
    (hdataR : baseR+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*_root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.LightBlockQuery.sourceCut h J) ≤ masks)
    (hindex : indexBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1) ≤ masks) (hptr : ptrBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1) ≤ masks)
    (hboxesEnd : boxBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1)*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1)) boxCut ≤ masks)
    (hmasks : masks+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ dstL) (hleft : dstL+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ dstR)
    (hright : dstR+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ dst) (hdst : dst+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ selected)
    (hselected : selected+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ maskBase)
    (hqueryMasks : maskBase+_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J (k+1)) t ≤ work)
    (hspace : work+1+_root_.ThreeSum.LightPascal.tableSize (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1) ≤ lim.space)
    (hpowSpace : work+(2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+2) ≤ lim.space)
    (hemodSpace : work+(Nat.log 2 (_root_.ThreeSum.LightReportingCatalogLookup.valueBound (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1))+1)+2) ≤ lim.space)
    (hword : (((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hlookupWord : (_root_.ThreeSum.LightReportingCatalogLookup.word (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1)) : ℤ) ≤ lim.word)
    (hvalueWord : (_root_.ThreeSum.LightSparseQuery.magnitudeBound (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1)) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1))
      (_root_.ThreeSum.LightBlockQuery.residualSize h J (k+1)) t B.card C.card : ℤ) ≤ lim.word)
    (ht : t ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J (k+1)+1) (hboxCut : boxCut ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J (k+1))
    (hflags : _root_.ThreeSum.LightBlockQuery.residualSize h J (k+1)-t ≤ boxCut)
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL (_root_.ThreeSum.LightBlockQuery.sourceCut h J)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource pMod B b w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J))
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR (_root_.ThreeSum.LightBlockQuery.sourceCut h J)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource pMod shift C c w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J))
    (hindexData : ∃ S : List ℤ, _root_.ThreeSum1960614.Machine.Light.Seg μ indexBase S ∧
      S.Perm (_root_.ThreeSum.ReportingHostPackedCatalog.codes (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefixKey h J (k+1)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1))) ∧
      S.Pairwise (· ≤ ·))
    (hptrs : _root_.ThreeSum1960614.Machine.Light.SegN μ ptrBase (List.ofFn fun i : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1)) =>
      boxBase+i.val*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1)) boxCut))
    (hboxes : ∀ i < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1), _root_.ThreeSum.LightBoxStages.StoredThrough μ
      (boxBase+i*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1)) boxCut) boxCut
      (_root_.ThreeSum.ReportingHostSuffix.leafWeight (_root_.ThreeSum.ReportingHostSuffix.block_fit (Nat.succ_le_of_lt hk)) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource pMod B b w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource pMod shift C c w.2.2)
        (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1)) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J (k+1) i) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J (k+1) i))
      (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1)))
    (hd : depth+2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+15 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.program 46 depth
      [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J,h,_root_.ThreeSum.BlockMaskLayout.rowMask (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) ⟨k,hk⟩,
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)),
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)),
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)),masks,dstL,dstR,work,
        _root_.ThreeSum.LightBlockQuery.sourceCut h J,_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1),(k+1)*h,_root_.ThreeSum.LightBlockQuery.residualSize h J (k+1),
        t,baseL,baseR,boxCut,indexBase,ptrBase,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1),_root_.ThreeSum.LocalCoverBounds.groupSize h,dst,selected,maskBase,(k+1)*(464*h)]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time h J k t)
      (fun r μ' =>
        let counts := fun i => _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c)
          w (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childAt w.2.2 pre hk i)
        r = ((_root_.ThreeSum.LightReportingFilter.selected counts (_root_.ThreeSum.LocalCoverBounds.groupSize h)).length : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' selected (_root_.ThreeSum.LightReportingFilter.selected counts (_root_.ThreeSum.LocalCoverBounds.groupSize h)) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dst (List.ofFn fun i : Fin (_root_.ThreeSum.LocalCoverBounds.groupSize h) => counts i.val) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' masks ((_root_.ThreeSum.ReportingHostMasks.globalChildren ⟨k,hk⟩ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2 ⟨k,hk⟩) h).map _root_.ThreeSum.SubsetAddress.subsetMask) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dstL ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes w.2.2 pre hk).map fun next =>
          _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix (k+1) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dstR ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes w.2.2 pre hk).map fun next =>
          _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ μ' masks) := by sorry
