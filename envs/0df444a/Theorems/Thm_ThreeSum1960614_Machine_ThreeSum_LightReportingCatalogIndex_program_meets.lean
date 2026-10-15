-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingCatalogIndex_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:37:22.845288+00:00
-- url     : https://prove2.me/theorems/dbe67b72-ad4e-4b56-93f3-27eeb7258b89
-- title:
--   Construction and sorting of a complete prefix-catalog index
-- statement:
--   Let $h,J,k$ be natural parameters with $k\le J$. Let two integer functions on subsets of width $464hJ$ be bounded by $B,D$ through source cutoff $c$, with their stages stored. Suppose the suffix box cutoff fits the remaining width and $kh$ plus that cutoff is at most $c$. Assume the exact ordered allocations for local pair rows, both positional products, pointer and box arrays, masks, index, and scratch; the stated pair, Pascal, sort-space, power, key, index and value-word bounds; and all pair/query/sort depth allowances. The closed program constructs the full aligned prefix catalog, writes its exact count and pointer array, builds every suffix-box stage family, and stores a sorted permutation of all packed prefix keys retaining original indices. It returns the product-header address, retains both source-stage families, and preserves the preceding input region within its stated time.
--
--   Builds the actual shared catalog and its logarithmic-access index without a supplied prefix enumeration. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingCatalogIndex.lean#L40-L150

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
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSortedCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSortedCatalog


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingCatalogIndex
end ThreeSum.LightReportingCatalogIndex
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
set_option maxHeartbeats 1500000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex.program_meets {μ : ℕ → ℤ}
    {h J k cut boxCut baseL baseR srcS pairL pairR stageL stageR ptrBase boxBase maskBase indexBase work B D d : ℕ}
    (hk : k ≤ J) (f g : Finset (Fin (J*(464*h))) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : cut ≤ J*(464*h)) (hboxCut : boxCut ≤ (J-k)*(464*h))
    (hdataL : baseL+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ srcS)
    (hdataR : baseR+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ srcS)
    (hS : srcS+(464*h).choose h ≤ pairL)
    (hL : pairL+_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h ≤ pairR)
    (hR : pairR+_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h ≤ stageL)
    (hstageL : _root_.ThreeSum.LightRadixKeys.space stageL (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h) k ≤ stageR)
    (hstageR : _root_.ThreeSum.LightRadixKeys.space stageR (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h) k ≤ ptrBase)
    (hptr : ptrBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ boxBase)
    (hbox : boxBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*_root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) boxCut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.SubsetAddress.downsetCap ((J-k)*(464*h)) boxCut ≤ work)
    (hindex : maskBase ≤ indexBase) (hindexEnd : indexBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ work)
    (hpairSpace : work+2*(464*h)+2 ≤ lim.space)
    (hspace : work+1+_root_.ThreeSum.LightPascal.tableSize (J*(464*h))+(J*(464*h)+1) ≤ lim.space)
    (hsortSpace : work+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ lim.space)
    (hpowWord : ((2^(464*h+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (_root_.ThreeSum.LightRadixKeys.word (2^(464*h)) (2^(464*h)) k : ℤ) ≤ lim.word)
    (hword : (((J*(464*h)+1)*2^(J*(464*h)+1) : ℕ) : ℤ) ≤ lim.word)
    (hindexWord : (_root_.ThreeSum.LightReportingSortedCatalog.word (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^((J-k)*(464*h))*
      ((2^((J-k)*(464*h))*B)*(2^((J-k)*(464*h))*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpre : k*h+boxCut ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B) (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL cut f (J*(464*h)))
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR cut g (J*(464*h)))
    (hdPair : d+464*h+k+6 ≤ lim.depth) (hd : d+J*(464*h)+15 ≤ lim.depth)
    (hdSort : d+Nat.clog 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k)+3 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex.program 51 d
      [J*(464*h),cut,boxCut,(J-k)*(464*h),(J-k)*(464*h),k*(464*h),baseL,baseR,
        464*h,h,k,srcS,pairL,pairR,stageL,stageR,ptrBase,boxBase,maskBase,work,indexBase]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex.time h J k boxCut)
      (fun r μ' =>
        r = (stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h) k : ℕ) ∧
        μ' (stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h) k) = (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' ptrBase (List.ofFn fun i : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) =>
          boxBase+i.val*_root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) boxCut) ∧
        (∀ i < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k, _root_.ThreeSum.LightBoxStages.StoredThrough μ'
          (boxBase+i*_root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) boxCut) boxCut
          (_root_.ThreeSum.ReportingHostSuffix.leafWeight (_root_.ThreeSum.ReportingHostSuffix.block_fit hk) f g ((J-k)*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i))
          ((J-k)*(464*h))) ∧
        _root_.ThreeSum.LightZetaStages.StoredThrough μ' baseL cut f (J*(464*h)) ∧
        _root_.ThreeSum.LightZetaStages.StoredThrough μ' baseR cut g (J*(464*h)) ∧
        (∃ S : List ℤ, _root_.ThreeSum1960614.Machine.Light.Seg μ' indexBase S ∧
          S.Perm (_root_.ThreeSum.ReportingHostPackedCatalog.codes (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefixKey h J k) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k)) ∧
          S.Pairwise (· ≤ ·)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ μ' srcS) := by sorry
