-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingGatherPair_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingGatherPair.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:39:52.717634+00:00
-- url     : https://prove2.me/theorems/47fd4b76-d4d4-4800-9f21-d137ebb3d925
-- title:
--   Execution of aligned paired-mask gathering
-- statement:
--   Let $i_s<n$ for $s<t$ be selected indices, and let integer arrays $L,R$ of length $n$ be correctly stored with those indices in memory $\mu$. Let the two length-$t$ output arrays fit memory and be disjoint from each other and the index row. The left output is disjoint from both source rows, and the right output is disjoint from its right source row. Assume every segment fits, addresses fit words, all source values fit words and a nested call is allowed. The fixed paired-gather program writes
--
--   $$[L_{i_s}]_{s<t},\qquad[R_{i_s}]_{s<t}$$
--
--   within its specified $t$-dependent time, changing only those two output intervals.
--
--   This keeps selected left and right reporting-prefix masks aligned in physical memory.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingGatherPair.lean#L18-L49

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightReportingGatherPair
end ThreeSum.LightReportingGatherPair
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingGatherPair
end ThreeSum1960614.Machine.ThreeSum.LightReportingGatherPair

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingGatherPair
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingGatherPair

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingGatherPair.program_meets {μ : ℕ → ℤ} {indices srcL srcR dstL dstR t n d : ℕ}
    (index : ℕ → ℕ) (left right : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hindices : indices+t ≤ lim.space) (hsrcL : srcL+n ≤ lim.space) (hsrcR : srcR+n ≤ lim.space)
    (hdstL : dstL+t ≤ lim.space) (hdstR : dstR+t ≤ lim.space)
    (hsepIL : _root_.Light.Apart indices t dstL t) (hsepIR : _root_.Light.Apart indices t dstR t)
    (hsepLL : _root_.Light.Apart srcL n dstL t) (hsepRL : _root_.Light.Apart srcR n dstL t)
    (hsepRR : _root_.Light.Apart srcR n dstR t) (hsepOut : _root_.Light.Apart dstL t dstR t)
    (hindex : ∀ i < t, index i < n)
    (hreadI : ∀ i < t, μ (indices+i) = (index i : ℤ))
    (hreadL : ∀ i < n, μ (srcL+i) = left i) (hreadR : ∀ i < n, μ (srcR+i) = right i)
    (hwordL : ∀ i < n, |left i| ≤ lim.word) (hwordR : ∀ i < n, |right i| ≤ lim.word)
    (hd : d < lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingGatherPair.program 1 d [indices,srcL,srcR,t,n,dstL,dstR] μ (_root_.ThreeSum.LightReportingGatherPair.time t)
      (fun _ ν => _root_.ThreeSum1960614.Machine.Light.Seg ν dstL (List.ofFn fun i : Fin t => left (index i.val)) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg ν dstR (List.ofFn fun i : Fin t => right (index i.val)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside2 μ ν dstL t dstR t) := by sorry
