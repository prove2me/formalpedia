-- Prove2me | Theorems.Thm_PiecesCounted_padThen_runs
-- name    : PiecesCounted.padThen_runs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:00:00.368913+00:00
-- url     : https://prove2.me/theorems/3c89643d-9311-4f21-9338-e46b9130f89c
-- title:
--   Pieces Counted: pad Then runs
-- statement:
--   The machine halts within N a + 1 steps with the value of f at N a units; S bounds the input with
--   the number and the units, and the result.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/PadThen.lean#L70-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/PadThen.lean#L70-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_PiecesCounted_Sizes
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_PadThen
set_option autoImplicit false
section
section
open PiecesCounted
open Groundwork
variable {α β : Type}

theorem PiecesCounted.padThen_runs [HasSize α] [HasSize β] (N : α → ℕ) (f : α × List Unit → β) (a : α) {S : ℕ} (h1 : size a + size (N a) + (2 * N a + 1) + 1 ≤ S)
    (h2 : size (f (a, List.replicate (N a) ())) + 1 ≤ S) : (padThen N f).Runs a (N a + 1) S (f (a, List.replicate (N a) ())) := by sorry
