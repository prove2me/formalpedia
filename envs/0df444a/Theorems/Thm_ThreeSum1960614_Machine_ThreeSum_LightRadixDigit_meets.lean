-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightRadixDigit_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightRadixDigit.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:35:57.953503+00:00
-- url     : https://prove2.me/theorems/ad98f1bb-e5f9-4fc4-a96c-3f940d06d761
-- title:
--   Execution of radix-digit extraction
-- statement:
--   Let $k,b,p\in\mathbb N$, $\mu$ an integer memory, and $\lambda,P,d$ limits, program and depth. Suppose the program contains the radix-digit body and small-division helper, a nested call is allowed, and the explicit digit word envelope fits. The call returns
--
--   $$\left\lfloor k/b\right\rfloor\bmod p$$
--
--   within its stated $k$-dependent time, leaving memory unchanged. Both natural division and remainder use their total conventions, including zero parameters.
--
--   This implements exact ordered coefficient and record digit decoding.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightRadixDigit.lean#L19-L82

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Log
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSmallDivide_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightRadixDigit
end ThreeSum.LightRadixDigit
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightRadixDigit
end ThreeSum1960614.Machine.ThreeSum.LightRadixDigit

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightRadixDigit
open _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixDigit

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightRadixDigit.meets {pMain pDivide k b p : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body) (μ : ℕ → ℤ)
    (hd : d < lim.depth) (hword : (_root_.ThreeSum.LightRadixDigit.word k b p : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [k,b,p] μ (_root_.ThreeSum.LightRadixDigit.time k)
      (fun r μ' => r = (((k/b)%p : ℕ) : ℤ) ∧ μ'=μ) := by sorry
