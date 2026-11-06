-- Prove2me | Theorems.Thm_PiecesCounted_shift_zero_lt
-- name    : PiecesCounted.shift_zero_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:08:55.240938+00:00
-- url     : https://prove2.me/theorems/54be7f21-841a-4628-8733-97654f58be76
-- title:
--   Pieces Counted: shift zero lt
-- statement:
--   The condition on the shift, for the shift 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/EightSquare.lean#L42-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/EightSquare.lean#L42-L45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Padded
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_PiecesFromEightSquares_LemPieces
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_EightSquare
set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.shift_zero_lt (c lam : ℕ) : |(0 : ℤ)| + (2 * lam) ^ c < 2 ^ (2 * lam) ^ c := by sorry
