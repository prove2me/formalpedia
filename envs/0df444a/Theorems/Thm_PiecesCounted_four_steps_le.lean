-- Prove2me | Theorems.Thm_PiecesCounted_four_steps_le
-- name    : PiecesCounted.four_steps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:23:14.029102+00:00
-- url     : https://prove2.me/theorems/f5bd8682-b262-47ba-94e3-9f96e1bf4fde
-- title:
--   Pieces Counted: four steps le
-- statement:
--   4·2^{cλ} ≤ 2^{(c+2)λ} for λ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L204-L209
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L204-L209

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_GeneralPieces_Trim_Prog
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Trimmed
set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.four_steps_le (c : ℕ) {lam : ℕ} (hl : 1 ≤ lam) : 4 * steps c lam ≤ steps (c + 2) lam := by sorry
