-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightNatPower_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightNatPower.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:47:32.931422+00:00
-- url     : https://prove2.me/theorems/e374a29e-e979-44a6-a24d-0ac95e1d455d
-- title:
--   Execution of natural exponentiation
-- statement:
--   Let $b,e\in\mathbb N$, $\mu$ any integer memory, and $\lambda,P,d$ limits, program and depth. If procedure $p$ is the power body, $e$ fits a word and every $b^i$ for $i\le e$ fits a word, then
--
--   $$\operatorname{result}=b^e$$
--
--   within its prescribed exponent-dependent time, with the entire memory unchanged.
--
--   This realizes the scalar powers needed for finite counts, moduli and representation caps.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightNatPower.lean#L24-L56

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1962Source_Bundle02
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightNatPower
end ThreeSum.LightNatPower
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightNatPower
end ThreeSum1960614.Machine.ThreeSum.LightNatPower

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightNatPower
open _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightNatPower.meets {p b e : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body) (μ : ℕ → ℤ)
    (he : (e : ℤ) ≤ lim.word)
    (hpow : ∀ i ≤ e, ((b^i : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [b,e] μ (_root_.ThreeSum.LightNatPower.time e)
      (fun r μ' => r = ((b^e : ℕ) : ℤ) ∧ μ' = μ) := by sorry
