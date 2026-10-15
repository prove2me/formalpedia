-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_while
-- name    : ThreeSum1960614.Machine.Light.Ends.while
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:08:12.656866+00:00
-- url     : https://prove2.me/theorems/77af110e-fe32-4fed-a621-0d36a36a62e2
-- title:
--   A bounded while loop with round-dependent costs
-- statement:
--   Let $\ell,P,d$ be Light limits, program, and call depth; let $c$ be a condition, $s$ a body, and $I(i,\sigma)$ an invariant. Suppose $I(0,\sigma_0)$; for every $i<n$, the invariant makes $c$ safe and true and the body reaches $I(i+1)$ within $b(i)$ steps; and at $i=n$ the condition is safe and false and the final postcondition $Q$ holds. Then the while loop reaches $Q$ within $$\sum_{i<n}(\operatorname{cost}(c)+1+b(i))+\operatorname{cost}(c)+1.$$
--
--   Provides the exact finite-loop rule used throughout the concrete procedure proofs. This is a supporting lemma in the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Logic.lean#L134-L161

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
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

theorem ThreeSum1960614.Machine.Light.Ends.while {σ c s} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (I : ℕ → _root_.ThreeSum1960614.Machine.Light.State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ (b i) (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.while c s) σ (∑ i ∈ Finset.range n, (c.cost + 1 + b i) + (c.cost + 1)) Q := by sorry
