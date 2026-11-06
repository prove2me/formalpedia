-- Prove2me | Theorems.Thm_PiecesCounted_toBits_take
-- name    : PiecesCounted.toBits_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:00:06.6831+00:00
-- url     : https://prove2.me/theorems/0202a6c0-ddc0-4e0b-9f86-9e3c5b3e4d5e
-- title:
--   Pieces Counted: to Bits take
-- statement:
--   The first half of two strings written one after the other.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L82-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L82-L83

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

theorem PiecesCounted.toBits_take {n : ℕ} (x y : Pieces.Bits n) : toBits n ((bitsOf x ++ bitsOf y).take n) = x := by sorry
