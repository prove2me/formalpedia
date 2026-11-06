-- Prove2me | Theorems.Thm_PiecesCounted_padThen_reaches
-- name    : PiecesCounted.padThen_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:59:49.204138+00:00
-- url     : https://prove2.me/theorems/2b99e26c-b8a2-4af7-9e4f-0392c7c5144a
-- title:
--   Pieces Counted: pad Then reaches
-- statement:
--   From the state with j units written, where j + k = N a, the machine halts after k + 1 more steps
--   with the value of f at N a units.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/PadThen.lean#L42-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/PadThen.lean#L42-L66

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

theorem PiecesCounted.padThen_reaches [HasSize α] [HasSize β] (N : α → ℕ) (f : α × List Unit → β) (a : α) {S : ℕ} (h1 : size a + size (N a) + (2 * N a + 1) + 1 ≤ S)
    (h2 : size (f (a, List.replicate (N a) ())) + 1 ≤ S) (k : ℕ) :
    ∀ j, j + k = N a → (padThen N f).Reaches S (f (a, List.replicate (N a) ())) (.inl (a, N a, List.replicate j ())) (k + 1) := by sorry
