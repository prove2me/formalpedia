-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceFlagTest_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:38:41.314021+00:00
-- url     : https://prove2.me/theorems/8a897c24-ccf2-48ec-a683-e1b38647e94a
-- title:
--   Execution of the independent source-trimming flag
-- statement:
--   Let $c,k,n,B\in\mathbb N$ denote an observed cardinality, required cardinality, bucket count and cap. Let $\mu$ be any integer memory, and $\lambda,P,d$ be limits, program and depth, with procedure $p$ equal to the flag-test body. If $c+k+n+B+2$ fits the word bound, the procedure takes at most $25$ steps, leaves memory unchanged, and returns
--
--   $$\mathbf1_{\{c=k\ \wedge\ n\le B\}}.$$
--
--   This implements the independent cardinality-and-bucket trimming condition for each endpoint.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceFlagTest.lean#L30-L47

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
namespace ThreeSum.LightSourceFlagTest
end ThreeSum.LightSourceFlagTest
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest
end ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceFlagTest
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.meets {p card required count cap : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.body) (μ : ℕ → ℤ)
    (hword : ((card+required+count+cap+2 : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [card,required,count,cap] μ _root_.ThreeSum.LightSourceFlagTest.time
      (fun r ν => r = (_root_.ThreeSum.LightSourceFlagTest.flag card required count cap : ℤ) ∧ ν=μ) := by sorry
