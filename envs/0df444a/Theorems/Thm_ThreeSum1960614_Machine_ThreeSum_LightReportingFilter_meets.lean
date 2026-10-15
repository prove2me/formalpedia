-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingFilter_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingFilter.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:29:43.635978+00:00
-- url     : https://prove2.me/theorems/1c75c5d2-8b9b-49fd-b1fc-29873496381b
-- title:
--   Execution of positive-count filtering
-- statement:
--   Let $n,s,b,d\in\mathbb N$, $c:\mathbb N\to\mathbb N$, and $\lambda,P,\mu$ be run limits, program and memory. Suppose the filter body is in the program, addresses fit words, disjoint length-$n$ source and destination segments fit memory, and source cell $s+i$ stores $c(i)$ within the word bound for every $i<n$. The procedure writes the ordered selected indices
--
--   $$[\,i<n:c(i)>0\,]$$
--
--   at $b$, returns their count within its prescribed scan time, and changes no cell outside the length-$n$ destination reservation.
--
--   This realizes the positive-frontier selection used by output-sensitive reporting.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingFilter.lean#L59-L110

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
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightReportingFilter
end ThreeSum.LightReportingFilter
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingFilter
end ThreeSum1960614.Machine.ThreeSum.LightReportingFilter

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingFilter
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFilter

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingFilter.meets {p n src dst d : ℕ} {μ : ℕ → ℤ} (count : ℕ → ℕ)
    (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFilter.body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : _root_.Light.Apart src n dst n)
    (hword : ∀ i < n, (count i : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = (count i : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [n,src,dst] μ (_root_.ThreeSum.LightReportingFilter.time n)
      (fun r μ' => r = ((_root_.ThreeSum.LightReportingFilter.selected count n).length : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dst (_root_.ThreeSum.LightReportingFilter.selected count n) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst n) := by sorry
