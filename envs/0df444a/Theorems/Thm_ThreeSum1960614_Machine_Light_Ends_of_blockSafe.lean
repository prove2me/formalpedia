-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_of_blockSafe
-- name    : ThreeSum1960614.Machine.Light.Ends.of_blockSafe
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:08:17.47541+00:00
-- url     : https://prove2.me/theorems/2e52e2e3-7fd5-4a11-b9ec-3393026cd39f
-- title:
--   Safe blocks establish timed execution
-- statement:
--   For limits $L$, program $P$, depth $d$, statement $s$, initial state $\sigma$, budget $T$, and postcondition $Q$, block safety, $\operatorname{blockCost}(s)\le T$, and $Q(\operatorname{after}(s,\sigma))$ imply timed execution of $s$ establishing $Q$.
--
--   This rule turns verified straight-line blocks into the timed execution assertions used throughout the concrete programs.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Rules.lean#L138-L154

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.Light.Ends.of_blockSafe : ∀ {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}, s.BlockSafe lim σ →
    s.blockCost ≤ T → Q (s.after σ) → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q
  := by sorry
