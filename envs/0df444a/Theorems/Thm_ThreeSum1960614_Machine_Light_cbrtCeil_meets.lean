-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_cbrtCeil_meets
-- name    : ThreeSum1960614.Machine.Light.cbrtCeil_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:51:52.174811+00:00
-- url     : https://prove2.me/theorems/b63b930b-61c1-4e40-b5d2-b917bfed2857
-- title:
--   Computing the ceiling cube root
-- statement:
--   For natural $n$, assume the cube-root body is installed and $8n+1$ fits a word. The call returns the defined least cube-root ceiling $\operatorname{cbrtLeast}(n)$ within its stated time and preserves memory.
--
--   This arithmetic procedure supplies the rounded cube-root scale used by the executed initial block schedule.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L207-L237

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
import Theorems.Thm_Light_cbrtLeast_pow_le

namespace ThreeSum1960614.Machine.Light.Ends
end ThreeSum1960614.Machine.Light.Ends


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

theorem ThreeSum1960614.Machine.Light.cbrtCeil_meets {p n : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.cbrtCeilBody) (μ : ℕ → ℤ)
    (hword : ((8 * n + 1 : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [n] μ (_root_.Light.cbrtCeilTime n) fun r μ' => r = (_root_.Light.cbrtLeast n : ℤ) ∧ μ' = μ := by sorry
