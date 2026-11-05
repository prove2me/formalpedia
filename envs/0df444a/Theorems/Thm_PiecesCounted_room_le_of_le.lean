-- Prove2me | Theorems.Thm_PiecesCounted_room_le_of_le
-- name    : PiecesCounted.room_le_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:19:03.643211+00:00
-- url     : https://prove2.me/theorems/d32079f8-adde-4cc3-b14c-40bce6c07a22
-- title:
--   Pieces Counted: room le of le
-- statement:
--   The bound on the states grows with c, for λ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Basic.lean#L41-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Basic.lean#L41-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Basic
set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.room_le_of_le {c c' lam : ℕ} (hl : 1 ≤ lam) (h : c ≤ c') : room c lam ≤ room c' lam := by sorry
