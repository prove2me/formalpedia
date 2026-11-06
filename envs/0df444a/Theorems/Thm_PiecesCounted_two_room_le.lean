-- Prove2me | Theorems.Thm_PiecesCounted_two_room_le
-- name    : PiecesCounted.two_room_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:00:41.53765+00:00
-- url     : https://prove2.me/theorems/09f31db8-2a1e-4c16-9bdb-1813b7b5898b
-- title:
--   Pieces Counted: two room le
-- statement:
--   2·room c λ + 3 ≤ room (c + 2) λ for c, λ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L212-L226
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L212-L226

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

theorem PiecesCounted.two_room_le {c lam : ℕ} (hc : 1 ≤ c) (hl : 1 ≤ lam) : 2 * room c lam + 3 ≤ room (c + 2) lam := by sorry
