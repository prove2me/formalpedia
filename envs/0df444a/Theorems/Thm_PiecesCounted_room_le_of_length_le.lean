-- Prove2me | Theorems.Thm_PiecesCounted_room_le_of_length_le
-- name    : PiecesCounted.room_le_of_length_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:59:20.762081+00:00
-- url     : https://prove2.me/theorems/067bbb17-1fe4-4913-977d-d7762d201158
-- title:
--   Pieces Counted: room le of length le
-- statement:
--   The bound on the states grows with λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Basic.lean#L45-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Basic.lean#L45-L47

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

theorem PiecesCounted.room_le_of_length_le (c : ℕ) {lam lam' : ℕ} (h : lam ≤ lam') : room c lam ≤ room c lam' := by sorry
