-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingPositiveMasks_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:43:44.407855+00:00
-- url     : https://prove2.me/theorems/115c84e6-d1ce-42c9-bf0e-9e8f950e2f53
-- title:
--   Gathered positive masks equal the original next-prefix list
-- statement:
--   Let $I$ be a finite raw-incidence set over finite decidable types, $w$ a wanted label and $u$ a prefix at depth $k<J$, with microblock parameter $h$. Suppose memory stores the exact selected positive-child indices and the full ordered child left/right mask rows. Let $t$ be the selected-index length and $G(h)$ the full child count. Assume all index, source and two output segments fit memory; outputs are disjoint from each other and the index row; the left output is disjoint from both source rows and the right output from its right source; addresses fit words; $2^{J\cdot464h+1}$ fits a word; and a nested call is allowed. The paired gather writes exactly the left/right masks of the original positive-child prefix list, in order, within its $t$-dependent time and changes only those output intervals.
--
--   This identifies the actual packed positive arrays with the combinatorial next frontier.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingPositiveMasks.lean#L37-L102

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingGatherPair_program_meets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightReportingPositiveMasks
end ThreeSum.LightReportingPositiveMasks
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.program_meets {μ : ℕ → ℤ} {h J k indices srcL srcR dstL dstR d : ℕ}
    (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (pre : List (Finset (Fin (464*h)))) (hk : k < J)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hindices : indices+(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length ≤ lim.space)
    (hsrcL : srcL+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ lim.space) (hsrcR : srcR+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ lim.space)
    (hdstL : dstL+(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length ≤ lim.space)
    (hdstR : dstR+(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length ≤ lim.space)
    (hsepIL : _root_.Light.Apart indices (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length dstL (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length)
    (hsepIR : _root_.Light.Apart indices (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length dstR (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length)
    (hsepLL : _root_.Light.Apart srcL (_root_.ThreeSum.LocalCoverBounds.groupSize h) dstL (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length)
    (hsepRL : _root_.Light.Apart srcR (_root_.ThreeSum.LocalCoverBounds.groupSize h) dstL (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length)
    (hsepRR : _root_.Light.Apart srcR (_root_.ThreeSum.LocalCoverBounds.groupSize h) dstR (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length)
    (hsepOut : _root_.Light.Apart dstL (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length dstR (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length)
    (hreadI : _root_.ThreeSum1960614.Machine.Light.SegN μ indices (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk))
    (hreadL : _root_.ThreeSum1960614.Machine.Light.SegN μ srcL ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes w.2.2 pre hk).map fun next =>
      _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix (k+1) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))))
    (hreadR : _root_.ThreeSum1960614.Machine.Light.SegN μ srcR ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes w.2.2 pre hk).map fun next =>
      _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))))
    (hword : ((2^(J*(464*h)+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingGatherPair.program 1 d
      [indices,srcL,srcR,(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length,_root_.ThreeSum.LocalCoverBounds.groupSize h,dstL,dstR]
      μ (_root_.ThreeSum.LightReportingGatherPair.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length)
      (fun _ ν =>
        _root_.ThreeSum1960614.Machine.Light.SegN ν dstL ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk).map fun next =>
          _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix (k+1) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN ν dstR ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk).map fun next =>
          _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside2 μ ν dstL (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length dstR (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length) := by sorry
