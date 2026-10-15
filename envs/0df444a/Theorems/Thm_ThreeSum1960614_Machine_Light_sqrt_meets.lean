-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_sqrt_meets
-- name    : ThreeSum1960614.Machine.Light.sqrt_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:49:00.595573+00:00
-- url     : https://prove2.me/theorems/90e96c40-718f-4ae0-a80a-327ec3d106e5
-- title:
--   Computing the natural square root
-- statement:
--   For natural $K$, assume the square-root body is installed and $3K+4$ fits a word. The call returns $\lfloor\sqrt K\rfloor$ within the declared time and preserves memory.
--
--   This arithmetic contract supplies exact square-root values used by selected-prime and parameter initialization.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Sqrt.lean#L47-L77

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
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_of_blockSafe
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_while

namespace Light
end Light
namespace Light.Sqrt
end Light.Sqrt
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Sqrt
end ThreeSum1960614.Machine.Light.Sqrt

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.Light.sqrt_meets {p K : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.sqrtBody) (μ : ℕ → ℤ)
    (hword : ((3 * K + 4 : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [K] μ (_root_.Light.sqrtTime K) fun r μ' => r = (Nat.sqrt K : ℤ) ∧ μ' = μ := by sorry
