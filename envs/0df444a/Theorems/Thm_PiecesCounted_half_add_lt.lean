-- Prove2me | Theorems.Thm_PiecesCounted_half_add_lt
-- name    : PiecesCounted.half_add_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:02:34.752912+00:00
-- url     : https://prove2.me/theorems/1eb7ed2f-9a47-49ba-8c98-e2b50adb37d7
-- title:
--   Pieces Counted: half add lt
-- statement:
--   (n − 1)/2 + N < 2^N for n ≤ N, N ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Half.lean#L40-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Half.lean#L40-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Padded
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Half
set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.half_add_lt {n N : ℕ} (hn : n ≤ N) (hN : 1 ≤ N) : (n - 1) / 2 + N < 2 ^ N := by sorry
