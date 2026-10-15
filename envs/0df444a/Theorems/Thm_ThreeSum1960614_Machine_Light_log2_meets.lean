-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_log2_meets
-- name    : ThreeSum1960614.Machine.Light.log2_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:47:25.900251+00:00
-- url     : https://prove2.me/theorems/7f4e1856-8e91-4156-96db-d33390466c03
-- title:
--   Computing the binary logarithm
-- statement:
--   For natural $x$, assume the binary-logarithm body is installed at procedure $p$ and $2x+2$ fits a word. Its call on $x$ returns $\lfloor\log_2x\rfloor$, using the natural logarithm convention at zero, within its declared time and preserves memory.
--
--   This arithmetic procedure computes the exact input bit count used by the integer parameter schedule.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L62-L94

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

theorem ThreeSum1960614.Machine.Light.log2_meets {p x : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.log2Body) (μ : ℕ → ℤ)
    (hword : ((2 * x + 2 : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [x] μ (_root_.Light.log2Time x) fun r μ' => r = (Nat.log 2 x : ℤ) ∧ μ' = μ := by sorry
