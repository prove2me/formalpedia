-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceBucketOffsets_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOffsets.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:17:33.531985+00:00
-- url     : https://prove2.me/theorems/169d5f87-f4ef-445d-a20b-559c6b68e798
-- title:
--   Execution of bucket prefix offsets and initial cursors
-- statement:
--   Let $c:\mathbb N\to\mathbb N$, $N,M\in\mathbb N$, and histogram, offset and cursor bases $a_h,a_o,a_c$ be given. Suppose the histogram in memory $\mu$ counts every code $c(i)<M$ for $i<N$, the regions satisfy $a_h+M\le a_o$ and $a_o+M+1\le a_c$, and $a_c+M$ fits memory. Let $\lambda,P,d$ be limits, program and depth with the offset body present, addresses fitting words and $N$ fitting a word. The routine writes
--
--   $$\nu(a_o+r)=\operatorname{offset}(c,N,r)\ (r\le M),\qquad\nu(a_c+r)=\operatorname{offset}(c,N,r)\ (r<M),$$
--
--   within its specified $M$-dependent time, changing no cell outside $[a_o,a_c+M)$.
--
--   This constructs exact contiguous bucket boundaries from actual histogram counts.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceBucketOffsets.lean#L36-L113

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceBucketOffsets
end ThreeSum.LightSourceBucketOffsets
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOffsets
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOffsets
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceBucketOffsets
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOffsets

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOffsets.meets {pMain : ℕ} (hmain : P[pMain]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOffsets.body)
    {μ : ℕ → ℤ} {hist offsets cursor M N : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hN : (N : ℤ) ≤ lim.word)
    (hhist : hist+M ≤ offsets) (hoffsets : offsets+M+1 ≤ cursor)
    (hspace : cursor+M ≤ lim.space)
    (hkey : ∀ i < N, key i < M)
    (hread : ∀ r < M, μ (hist+r) = (_root_.ThreeSum.LightHistogram.count key r N : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [hist,offsets,cursor,M,N] μ (_root_.ThreeSum.LightSourceBucketOffsets.time M)
      (fun _ ν => (∀ r ≤ M, ν (offsets+r) = (_root_.ThreeSum.SourceBuckets.offset key N r : ℤ)) ∧
        (∀ r < M, ν (cursor+r) = (_root_.ThreeSum.SourceBuckets.offset key N r : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν offsets (cursor+M-offsets)) := by sorry
