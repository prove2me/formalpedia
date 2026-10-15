-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceControlsMax_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSourceControlsMax.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:31:46.003934+00:00
-- url     : https://prove2.me/theorems/0e3509fa-b535-4afa-bb6b-3644866c1504
-- title:
--   Memory-preserving maximum routine
-- statement:
--   Let $a,b\in\mathbb N$, $\mu$ be any integer memory, and $\lambda,P,d$ be run limits, a Light program and call depth. If procedure $p$ of $P$ is the maximum body and $\max(a,b)$ fits the word bound, then
--
--   $$\operatorname{result}=\max(a,b),\qquad\operatorname{steps}\le40,$$
--
--   and the entire memory is unchanged.
--
--   This provides a concrete scalar maximum operation for computing source-control dimensions.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceControlsMax.lean#L13-L26

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
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

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSourceControlsMax
end ThreeSum.LightSourceControlsMax
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceControlsMax
end ThreeSum1960614.Machine.ThreeSum.LightSourceControlsMax

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsMax

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceControlsMax.meets {p a b : ℕ} (hp : P[p]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsMax.body) (μ : ℕ → ℤ)
    (hword : ((max a b : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [a,b] μ 40 (fun r ν => r=((max a b : ℕ) : ℤ) ∧ ν=μ) := by sorry
