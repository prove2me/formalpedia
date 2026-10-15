-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingPrefixArrays_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:53:21.885584+00:00
-- url     : https://prove2.me/theorems/7a9bea1f-0f6e-4eec-84e6-c7abe30179f7
-- title:
--   Execution of all ordered prefix endpoint arrays
-- statement:
--   Let $L,h,k\in\mathbb N$ with $2h\le L$, and let $\lambda,\mu,d$ be limits, memory and depth. Reserve in order a cardinality-$h$ subset row, two local endpoint-mask rows, two radix-product stage areas, and scratch of $2L+2$ cells. Assume each earlier reservation ends before the next, the two radix areas meet their exact product-space requirements, addresses fit words, $2^{L+1}$ and the radix-key word budget fit, and $d+L+k+4$ is allowed. The fixed prefix-array program builds both ordered k-fold radix-$2^L$ endpoint lists, writes their common count $N(L,h)^k$, returns the left count-cell address, meets its prescribed time and preserves cells below the first subset-row base.
--
--   This constructs all physical reporting-prefix endpoint pairs in the exact original order.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingPrefixArrays.lean#L38-L125

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_powTable_ends
import Theorems.Thm_Light_seg_append
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightRadixKeys_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingPairRows_program_meets
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_leftAt_card
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_lefts_length
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_pairs_length
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_rights_length

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixArrays
end ThreeSum.LightReportingPrefixArrays
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.ReportingHostPairSegments
end ThreeSum.ReportingHostPairSegments
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingPrefixArrays
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum.ReportingHostPairSegments
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program_meets {μ : ℕ → ℤ} {L h k srcS pairL pairR stageL stageR work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hh : 2*h ≤ L)
    (hS : srcS+L.choose h ≤ pairL)
    (hL : pairL+_root_.ThreeSum.LightReportingPrefixArrays.localCount L h ≤ pairR) (hR : pairR+_root_.ThreeSum.LightReportingPrefixArrays.localCount L h ≤ stageL)
    (hstageL : _root_.ThreeSum.LightRadixKeys.space stageL (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k ≤ stageR)
    (hstageR : _root_.ThreeSum.LightRadixKeys.space stageR (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k ≤ work)
    (hspace : work+2*L+2 ≤ lim.space)
    (hpowWord : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (_root_.ThreeSum.LightRadixKeys.word (2^L) (2^L) k : ℤ) ≤ lim.word)
    (hd : d+L+k+4 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program 10 d [L,h,k,srcS,pairL,pairR,stageL,stageR,work] μ (_root_.ThreeSum.LightReportingPrefixArrays.time L h k)
      (fun r μ' =>
        r = (stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k : ℕ) ∧
        μ' (stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k) = ((_root_.ThreeSum.LightReportingPrefixArrays.localCount L h)^k : ℕ) ∧
        μ' (stageR+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k) = ((_root_.ThreeSum.LightReportingPrefixArrays.localCount L h)^k : ℕ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg μ' (stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k+1)
          (_root_.ThreeSum.RadixKeyLists.values ((2^L : ℕ) : ℤ) (_root_.ThreeSum.ReportingHostPairSegments.leftMasks L h) k) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg μ' (stageR+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k+1)
          (_root_.ThreeSum.RadixKeyLists.values ((2^L : ℕ) : ℤ) (_root_.ThreeSum.ReportingHostPairSegments.rightMasks L h) k) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ μ' srcS) := by sorry
