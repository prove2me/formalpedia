-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_half_meets
-- name    : ThreeSum1960614.Machine.Light.half_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:25:19.594107+00:00
-- url     : https://prove2.me/theorems/83c346ed-c1fd-47e1-8a6f-7d4ad05ad5ba
-- title:
--   Computing the ceiling half
-- statement:
--   For natural $h$, assume the halving body is installed and $h+1$ fits a word. The call returns $$\left\lfloor\frac{h+1}{2}\right\rfloor$$ within its declared time and preserves memory.
--
--   This arithmetic procedure supplies the ceiling-half value used by recursive splitting and scale initialization.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L251-L271

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
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
namespace Light.Logs
end Light.Logs
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Logs
end ThreeSum1960614.Machine.Light.Logs

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
open _root_.Light.Logs
open _root_.ThreeSum1960614.Machine.Light.Logs

theorem ThreeSum1960614.Machine.Light.half_meets {p h : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.halfBody) (μ : ℕ → ℤ)
    (hword : ((h + 1 : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [h] μ (_root_.Light.halfTime h) fun r μ' => r = (((h + 1) / 2 : ℕ) : ℤ) ∧ μ' = μ := by sorry
