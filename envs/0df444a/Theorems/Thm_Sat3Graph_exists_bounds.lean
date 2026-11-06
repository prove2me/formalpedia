-- Prove2me | Theorems.Thm_Sat3Graph_exists_bounds
-- name    : Sat3Graph.exists_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:53:42.737782+00:00
-- url     : https://prove2.me/theorems/e443f47a-693d-4735-89ae-e185d4651321
-- title:
--   Sat3 Graph: exists bounds
-- statement:
--   **The arithmetic of all bounds.** Let δ₃ ≥ 0 and δ₃·A ≤ δ. There is c' such that, whenever N ≤
--   A·(n+1) and T ≤ c·2^{δ₃N}: c·(N+2)^c ≤ c'·(n+2)^{c'} and T ≤ c'·2^{δn}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Split.lean#L88-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Split.lean#L88-L119

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SizeCircuit_General
import Definitions.Def_GraphProblems_Engine
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Split
set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Eight.Width

theorem Sat3Graph.exists_bounds (A c : ℕ) {δ δ₃ : ℝ} (h0 : 0 ≤ δ₃) (hle : δ₃ * (A : ℝ) ≤ δ) : ∃ c' : ℕ, ∀ n N T : ℕ, N ≤ A * (n + 1) →
    (T : ℝ) ≤ c * (2 : ℝ) ^ (δ₃ * N) → c * (N + 2) ^ c ≤ c' * (n + 2) ^ c' ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n) := by sorry
