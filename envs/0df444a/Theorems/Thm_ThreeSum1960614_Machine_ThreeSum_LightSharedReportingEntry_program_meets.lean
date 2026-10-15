-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSharedReportingEntry_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:42:56.838151+00:00
-- url     : https://prove2.me/theorems/e988b050-d397-4fe7-8ea0-d3c74ca8723a
-- title:
--   Execution of one complete shared reporting entry
-- statement:
--   Let $h,J,k\in\mathbb N$ with $k\le J$, global width $W=J\cdot464h$, suffix width $V=(J-k)464h$, source cutoff $c\le W$, box cutoff $b\le V$ and switch parameter $t$ be given. Integer subset functions $f,g$ are bounded by $B,D$ through cutoff $c$, with $kh+b\le c$. Suppose memory contains both full source transforms and cells pointing to them, all below a five-cell record destination. Reserve in order that record, local subset/pair rows, two radix prefix areas, box pointers, all local box payloads, mask/index buffers and scratch. Assume the exact ordered nonoverlap bounds, local/global Pascal-power and sorting scratch bounds hold; $t$ and every stated power, radix, address, sorted-key and signed-value bound fit words; addresses fit words; and all pair/global/sort call-depth requirements are allowed. The fixed program constructs the complete entry with metadata $(t,b,\mathrm{boxBase},\mathrm{indexBase},\mathrm{ptrBase})$, sorted physical prefix index and exact box transforms, returns the prefix count, retains both source transforms and meets its stated time. Below the local subset base it changes only the five metadata cells.
--
--   This packages all reusable data for exact physical prefix queries into one persistent reporting entry.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSharedReportingEntry.lean#L42-L145

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
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
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSharedReportingEntry
end ThreeSum.LightSharedReportingEntry
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
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry
end ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

theorem ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry.program_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ → ℤ}
    {h J k cut boxCut baseL baseR cellL cellR srcS pairL pairR stageL stageR
      ptrBase boxBase maskBase indexBase work B D d t rec : ℕ}
    (hk : k ≤ J) (f g : Finset (Fin (J*(464*h))) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : cut ≤ J*(464*h)) (hboxCut : boxCut ≤ (J-k)*(464*h))
    (hcellL : cellL < rec) (hcellR : cellR < rec)
    (hdataL : baseL+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ rec)
    (hdataR : baseR+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ rec)
    (hrec : rec+5 ≤ srcS)
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
    (hvalueWord : (((2^((J-k)*(464*h))*
      ((2^((J-k)*(464*h))*B)*(2^((J-k)*(464*h))*D))) : ℕ) : ℤ) ≤ lim.word)
    (htWord : (t : ℤ) ≤ lim.word)
    (hpre : k*h+boxCut ≤ cut) (hf : ∀ S, S.card ≤ cut → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hleftRead : μ cellL=(baseL : ℤ)) (hrightRead : μ cellR=(baseR : ℤ))
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL cut f (J*(464*h)))
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR cut g (J*(464*h)))
    (hdPair : d+464*h+k+7 ≤ lim.depth) (hd : d+J*(464*h)+16 ≤ lim.depth)
    (hdSort : d+Nat.clog 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k)+4 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry.program 52 d
      [J*(464*h),cut,boxCut,(J-k)*(464*h),(J-k)*(464*h),k*(464*h),cellL,cellR,
        464*h,h,k,srcS,pairL,pairR,stageL,stageR,ptrBase,boxBase,maskBase,work,indexBase,t,rec]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry.time h J k boxCut) (fun r ν =>
        r=(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Entry ν rec ⟨t,boxCut,boxBase,indexBase,ptrBase⟩ hk f g ∧
        _root_.ThreeSum.LightZetaStages.StoredThrough ν baseL cut f (J*(464*h)) ∧
        _root_.ThreeSum.LightZetaStages.StoredThrough ν baseR cut g (J*(464*h)) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν srcS rec 5) := by sorry
