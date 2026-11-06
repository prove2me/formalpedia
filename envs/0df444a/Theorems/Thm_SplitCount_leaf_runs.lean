-- Prove2me | Theorems.Thm_SplitCount_leaf_runs
-- name    : SplitCount.leaf_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:34:13.094382+00:00
-- url     : https://prove2.me/theorems/a6501afb-19c3-48b2-9177-3548295c476f
-- title:
--   Split Count: leaf runs
-- statement:
--   **One leaf.** Let D count for 3-CNFs (proof of Corollary 6, first sentence) with exponent δ' ≥ 0
--   and constant A, let δ'·(1 + 3(max(k,3) − 3))·(Bl + 1) ≤ δ/3, and let the node x carry n in unary and
--   have at most Bl·n clauses
--   of at most max(k, 2) literals on x₀ … xₙ₋₁. Then the width reduction followed by D returns its
--   number of satisfying assignments on n variables within ⌊A·2^{(δ/3)n}⌋ steps, on states of size ≤
--   A·(`leafConst k Bl`·M²)^A, for all M ≥ 1 with n ≤ M.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Leaf.lean#L68-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Leaf.lean#L68-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_SplitCount_Width
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_SplitCount_Leaf
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight.Width Occ

theorem SplitCount.leaf_runs {k Bl A : ℕ} {D : StepMachine (List Unit × Fml) ℕ} {δ δ' : ℝ} (hδ' : 0 ≤ δ')
    (hδB : δ' * ((1 + 3 * (((max k 3 : ℕ) : ℝ) - 3)) * ((Bl : ℝ) + 1)) ≤ δ / 3) (hD : CountsThree D δ' A) {n M : ℕ} (hn : n ≤ M) (h1 : 1 ≤ M) {x : NNode}
    (hx1 : x.1 = List.replicate n ()) (hxl : (leafF x.2).length ≤ Bl * n) (hxc : ∀ C ∈ leafF x.2, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n) :
    (Stepped.mapIn leafPlain (Stepped.mapIn widthP D)).Runs x ⌊(A : ℝ) * (2 : ℝ) ^ (δ / 3 * n)⌋₊ (A * (leafConst k Bl * M ^ 2) ^ A) (cntN n (leafF x.2)) := by sorry
