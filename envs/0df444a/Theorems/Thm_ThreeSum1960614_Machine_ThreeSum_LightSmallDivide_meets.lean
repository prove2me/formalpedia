-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSmallDivide_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:25:38.701452+00:00
-- url     : https://prove2.me/theorems/cb0d676f-9943-4329-bf04-29e09eecf19b
-- title:
--   Execution of the natural-number division routine
-- statement:
--   Let $a,b\in\mathbb N$, $\mu$ an integer memory, and $\lambda,P,d$ limits, program and depth. If procedure $p$ is the small-division body and $a+b+2$ fits the word bound, it returns
--
--   $$r=\lfloor a/b\rfloor$$
--
--   within the specified division budget and leaves memory unchanged. Division is total natural-number division, so the statement includes $b=0$ with result zero.
--
--   This implements integer divisions used for finite schedule and layout computations on the division-free target language.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSmallDivide.lean#L26-L76

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_of_blockSafe
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_while

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSmallDivide
end ThreeSum.LightSmallDivide
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSmallDivide
end ThreeSum1960614.Machine.ThreeSum.LightSmallDivide

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSmallDivide
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets {p a b : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body) (μ : ℕ → ℤ)
    (hword : ((a+b+2 : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [a,b] μ (_root_.ThreeSum.LightSmallDivide.time a b)
      (fun r μ' => r = ((a/b : ℕ) : ℤ) ∧ μ' = μ) := by sorry
