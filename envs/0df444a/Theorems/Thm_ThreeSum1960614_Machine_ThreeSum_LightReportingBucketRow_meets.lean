-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingBucketRow_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:27:32.324708+00:00
-- url     : https://prove2.me/theorems/893e0f9f-40cd-400d-adb9-f2c5096eb4c8
-- title:
--   Counting matching original values through a selected index row
-- statement:
--   Let $\lambda,P,d,\mu$ be limits, program, depth and memory. Let $N,n,a_v,a_i\in\mathbb N$, target $z\in\mathbb Z$, value map $v:\mathbb N\to\mathbb Z$ and index map $j:\mathbb N\to\mathbb N$ be given. Suppose the program contains the bucket-row body, both source segments fit memory, addresses fit words, $j(i)<N$ for $i<n$, and the arrays store exactly $j(i)$ and $v(k)$. If all $|v(k)|$ for $k<N$ and $|z|$ fit words, it returns
--
--   $$|\{i<n:v(j(i))=z\}|$$
--
--   within its prescribed scan time, preserving all memory.
--
--   This scans only the selected original-index fiber during terminal exact-value checking.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingBucketRow.lean#L57-L102

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightReportingBucketRow
end ThreeSum.LightReportingBucketRow
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow
end ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingBucketRow
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow.meets {p src indices n N : ℕ} {μ : ℕ → ℤ}
    (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow.body) (target : ℤ) (value : ℕ → ℤ) (index : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+N ≤ lim.space) (hindices : indices+n ≤ lim.space)
    (hindex : ∀ i < n, index i < N)
    (hreadI : ∀ i < n, μ (indices+i) = (index i : ℤ))
    (hreadV : ∀ i < N, μ (src+i) = value i)
    (hvalues : ∀ i < N, |value i| ≤ lim.word) (htarget : |target| ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [target,src,indices,n,N] μ (_root_.ThreeSum.LightReportingBucketRow.time n)
      (fun r ν => r=(_root_.ThreeSum.LightReportingBucketRow.count target value index n : ℤ) ∧ ν=μ) := by sorry
