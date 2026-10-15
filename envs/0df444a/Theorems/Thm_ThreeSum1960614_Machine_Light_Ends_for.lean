-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
-- name    : ThreeSum1960614.Machine.Light.Ends.for
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:12:33.020221+00:00
-- url     : https://prove2.me/theorems/b437f18c-a389-40ea-b050-104ef93ebeb7
-- title:
--   A timed rule for counting loops
-- statement:
--   Let $i$ be the counter, $n$ the iteration count, $b$ a body-time bound, $I(j,\sigma)$ an invariant, and $Q$ the final postcondition. Assume initialization at zero, a body step preserving counter $j$ and establishing the next invariant after increment, termination at $n$, a safe upper-bound expression evaluating to $n$, and $n$ fitting a word. Then the loop establishes $Q$ whenever $$n(\operatorname{cost}(\mathrm{hi})+b+7)+\operatorname{cost}(\mathrm{hi})+5\le T.$$
--
--   This counting-loop rule accounts for tests, increments, body execution, and the terminal test in concrete program costs.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Rules.lean#L295-L338

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_while

namespace Light
end Light
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.Light.Ends.for {σ : _root_.ThreeSum1960614.Machine.Light.State} {i : ℕ} {hi : _root_.ThreeSum1960614.Machine.Light.Expr} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (I : ℕ → _root_.ThreeSum1960614.Machine.Light.State → Prop) (n b : ℕ)
    (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round : ∀ (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State), j < n → σ.loc i = j → I j σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d body σ b fun σ' =>
      σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : _root_.ThreeSum1960614.Machine.Light.State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State), j ≤ n → σ.loc i = j → I j σ → hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by (first
                                                         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                             first
                                                             | omega
                                                             | (ring_nf; omega))
                                                         | omega
                                                         |
                                                           (simp [] <;>
                                                               first
                                                               | omega
                                                               | (ring_nf; omega)))) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.for i hi body) σ T Q := by sorry
