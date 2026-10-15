-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceBucketSetup_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:14:31.432257+00:00
-- url     : https://prove2.me/theorems/c9466a90-c464-4329-86ac-3fe319098a25
-- title:
--   Setting up packed physical residue buckets
-- statement:
--   A length-$N$ key array with keys below positive $M$ precedes allocation base $b$. Under the exact next-free space bound, word-address bound, helper placement, and call-depth bound, the setup procedure builds the exact histogram, offsets, and physical index fibers at their computed addresses, returns the next free address, and preserves memory below $b$ in its stated time.
--
--   This generic setup provides complete physical fibers for both source reporting and wanted-record residue joins.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBucketSetup.lean#L43-L71

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceBucketBuild_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceBucketSetup
end ThreeSum.LightSourceBucketSetup
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceBucketSetup
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup.Procs.meets {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup.Procs P pMain)
    {μ : ℕ → ℤ} {keys N M base : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hM : 0 < M)
    (hkeys : keys+N ≤ base) (hspace : _root_.ThreeSum.LightSourceBucketSetup.next base N M ≤ lim.space)
    (hkey : ∀ i < N, key i < M) (hread : ∀ i < N, μ (keys+i) = (key i : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [keys,N,M,base] μ (_root_.ThreeSum.LightSourceBucketSetup.time N M)
      (fun r ν => r = (_root_.ThreeSum.LightSourceBucketSetup.next base N M : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored ν key N M (_root_.ThreeSum.LightSourceBucketSetup.offsets base M) (_root_.ThreeSum.LightSourceBucketSetup.flat base M) ∧
        (∀ j < M, ν (_root_.ThreeSum.LightSourceBucketSetup.hist base+j) = (_root_.ThreeSum.LightHistogram.count key j N : ℤ)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν base) := by sorry
