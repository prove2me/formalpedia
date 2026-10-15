-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSwitchScalar_scalar_safe
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.scalar_safe
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:03:09.685169+00:00
-- url     : https://prove2.me/theorems/7f8d40dc-b91a-4833-9f41-8fc887f034db
-- title:
--   Structural word safety of scalar switch expressions
-- statement:
--   Let $B\in\mathbb N$ with $B\ge2$, $\sigma$ a Light state, $\lambda$ run limits, and $e$ a scalar expression. Assume every local value satisfies $|\sigma_i|\le B$, every literal of $e$ is at most $B$, and $e$ uses only literals, variables and arithmetic operations, without memory loads. If its syntactic evaluation cost is $c(e)$ and
--
--   $$B^{c(e)}\le\lambda.\mathrm{word},$$
--
--   then every intermediate evaluation of $e$ stays within the run limits.
--
--   This supplies word-safety bounds for the fixed integer switching arithmetic.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSwitchScalar.lean#L62-L76

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
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

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSwitchScalar
end ThreeSum.LightSwitchScalar
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar
end ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1600000

theorem ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.scalar_safe {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {B : ℕ} (hB : 2 ≤ B) (σ : _root_.ThreeSum1960614.Machine.Light.State)
    (hvars : ∀ i, |σ.loc i| ≤ (B : ℤ)) (e : _root_.ThreeSum1960614.Machine.Light.Expr) (he : _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.Small B e)
    (hword : ((B^e.cost : ℕ) : ℤ) ≤ lim.word) : e.Safe lim σ := by sorry
