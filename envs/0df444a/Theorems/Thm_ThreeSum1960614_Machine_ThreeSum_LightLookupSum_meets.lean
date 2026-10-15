-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLookupSum_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightLookupSum.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:39:45.421707+00:00
-- url     : https://prove2.me/theorems/21dfd749-f4b3-403f-804d-f747bc6b5724
-- title:
--   Execution of a table-lookup sum
-- statement:
--   Let $\lambda,P,d,\mu$ be limits, program, depth and memory. Let $a_k,a_t,n,p,B\in\mathbb N$ be key/table bases, key count, table length and entry bound. Suppose procedure $q$ is the lookup-sum body, both arrays fit memory and addresses fit words; the keys equal $c_i<p$, table entries equal $f(r)\le B$, and $nB$ fits a word. The routine returns
--
--   $$\sum_{i<n}f(c_i)$$
--
--   within its prescribed linear scan budget and leaves memory unchanged.
--
--   This charges actual histogram lookups and accumulation in modular counting.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLookupSum.lean#L50-L92

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightLookupSum
end ThreeSum.LightLookupSum
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightLookupSum
end ThreeSum1960614.Machine.ThreeSum.LightLookupSum

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightLookupSum
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLookupSum

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open scoped _root_.BigOperators
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightLookupSum.meets {pThis : ℕ} (hThis : P[pThis]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightLookupSum.body)
    {μ : ℕ → ℤ} {keys table n p B : ℕ} (key f : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeys : keys+n ≤ lim.space) (htable : table+p ≤ lim.space)
    (hkey : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hrange : ∀ i < n, key i < p)
    (hread : ∀ r < p, μ (table+r) = (f r : ℤ))
    (hvalue : ∀ r < p, f r ≤ B)
    (hword : (n*B : ℕ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pThis d [keys, table, n, p] μ (_root_.ThreeSum.LightLookupSum.time n)
      fun r μ' => r = (_root_.ThreeSum.LightLookupSum.prefixSum f key n : ℤ) ∧ μ' = μ := by sorry
