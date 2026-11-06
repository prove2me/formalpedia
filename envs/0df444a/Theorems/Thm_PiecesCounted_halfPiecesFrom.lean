-- Prove2me | Theorems.Thm_PiecesCounted_halfPiecesFrom
-- name    : PiecesCounted.halfPiecesFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:22:03.486994+00:00
-- url     : https://prove2.me/theorems/0a97842b-a13b-46a4-8e82-2fa5e69ffced
-- title:
--   Pieces Counted: half Pieces From
-- statement:
--   `HalfPiecesFrom`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Half.lean#L47-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Half.lean#L47-L85

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

theorem PiecesCounted.halfPiecesFrom : HalfPiecesFrom := by sorry
