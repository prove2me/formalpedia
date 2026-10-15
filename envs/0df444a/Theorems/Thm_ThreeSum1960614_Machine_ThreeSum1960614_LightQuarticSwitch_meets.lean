-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum1960614_LightQuarticSwitch_meets
-- name    : ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:47:56.208245+00:00
-- url     : https://prove2.me/theorems/d0927423-aa20-40bf-8a45-46c78048148d
-- title:
--   Execution of the least acceptable integer quartic switch
-- statement:
--   Let $J,j,r\in\mathbb N$ with $j\le J$, and suppose the finite candidate set of integers $q\le\lfloor r/2\rfloor$ satisfying the cleared quartic inequality is nonempty. Let $P$ contain the quartic-switch body at procedure $p$, and let $\lambda,\mu,d$ be limits, memory and depth. If the explicit switch word budget for $(J,r)$ fits, the procedure returns
--
--   $$\min\{q\le\lfloor r/2\rfloor:\operatorname{accepts}(J,j,r,q)\}$$
--
--   within its prescribed $r$-dependent time and leaves memory unchanged.
--
--   This realizes the certified switching choice with finite integer arithmetic in the complete runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/QuarticSwitch.lean#L136-L165

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_of_blockSafe
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_while
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSwitchScalar_scalar_safe

namespace Light
end Light
namespace ThreeSum1960614
end ThreeSum1960614
namespace ThreeSum1960614.LightQuarticSwitch
end ThreeSum1960614.LightQuarticSwitch
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum1960614
end ThreeSum1960614.Machine.ThreeSum1960614
namespace ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch
end ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch

open _root_.ThreeSum1960614
open _root_.ThreeSum1960614.Machine.ThreeSum1960614

open _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {μ : ℕ→ℤ} {J j r q d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.meets {p : ℕ} (hp : P[p]?=some _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.body) (hj : j ≤ J)
    (hne : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r).Nonempty)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.word J r : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [J,j,r] μ (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.time r)
      (fun result ν => result=(_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index J j r : ℤ) ∧ ν=μ) := by sorry
