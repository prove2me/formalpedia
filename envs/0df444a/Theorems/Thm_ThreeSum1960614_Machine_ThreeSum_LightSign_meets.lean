-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSign_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSign.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:17:09.526366+00:00
-- url     : https://prove2.me/theorems/ec453e61-1f6b-4d6a-a5c3-b41df706d4e7
-- title:
--   Execution of a signed parity factor
-- statement:
--   Let $e\in\mathbb N$, $x\in\mathbb Z$, $\mu$ an integer memory, and $\lambda,P,d$ limits, program and depth. Suppose the program contains the sign body, addresses fit words, $e$ is within the address-space bound and $|x|$ fits a word. Then the procedure returns
--
--   $$(-1)^e x$$
--
--   within its stated parity-loop time, leaving all memory unchanged.
--
--   This implements the exact signs in subset-Moebius query evaluation.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSign.lean#L19-L47

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSign
end ThreeSum.LightSign
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSign
end ThreeSum1960614.Machine.ThreeSum.LightSign

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSign
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSign

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightSign.meets {pMain e d : ℕ} {x : ℤ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSign.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (he : e ≤ lim.space)
    (hvalue : |x| ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [x,e] μ (_root_.ThreeSum.LightSign.time e)
      (fun r μ' => r = (-1 : ℤ)^e*x ∧ μ' = μ) := by sorry
