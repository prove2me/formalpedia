-- Prove2me | Theorems.Thm_PiecesCounted_neg_half_polyT
-- name    : PiecesCounted.neg_half_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:02:45.072207+00:00
-- url     : https://prove2.me/theorems/56c3c9a6-f4ef-486d-8ff4-f39b1349a579
-- title:
--   Pieces Counted: neg half poly T
-- statement:
--   −⌊(f − 1)/2⌋ is polynomial-time if f is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Half.lean#L37-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Half.lean#L37-L37

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

theorem PiecesCounted.neg_half_polyT {f : List Unit → ℕ} (hf : PolyT f) : PolyT fun u => -(((f u - 1) / 2 : ℕ) : ℤ) := by sorry
