-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightTrimTest_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightTrimTest.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:03:17.152735+00:00
-- url     : https://prove2.me/theorems/a1da75e3-0791-41f5-89fd-30e63c820195
-- title:
--   Execution of the retained-edge trimming test
-- statement:
--   Let $x,l,r,b\in\mathbb N$ be overlap, left/right bucket counts and cap. For any memory $\mu$, limits $\lambda$, program $P$ and depth $d$, assume procedure $p$ is the trimming body and both $1$ and $b+1$ fit the word bound. Then it takes at most $30$ steps, leaves the entire memory unchanged, and returns
--
--   $$\mathbf1_{\{x=0\ \wedge\ l\le b\ \wedge\ r\le b\}}.$$
--
--   This realizes the exact retained local-edge predicate used by the deterministic cover matrix.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightTrimTest.lean#L32-L54

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
import Definitions.Def_ThreeSum1962Source_Bundle03
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

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightTrimTest
end ThreeSum.LightTrimTest
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightTrimTest
end ThreeSum1960614.Machine.ThreeSum.LightTrimTest

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightTrimTest
open _root_.ThreeSum1960614.Machine.ThreeSum.LightTrimTest

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightTrimTest.meets {p x l r b : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightTrimTest.body) (μ : ℕ → ℤ)
    (hword : (1 : ℤ) ≤ lim.word) (hcap : ((b+1 : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [x,l,r,b] μ _root_.ThreeSum.LightTrimTest.time
      (fun v μ' => v=(_root_.ThreeSum.LightTrimTest.flag x l r b : ℤ) ∧ μ'=μ) := by sorry
