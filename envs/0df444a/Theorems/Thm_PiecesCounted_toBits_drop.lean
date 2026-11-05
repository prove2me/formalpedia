-- Prove2me | Theorems.Thm_PiecesCounted_toBits_drop
-- name    : PiecesCounted.toBits_drop
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:00:29.568214+00:00
-- url     : https://prove2.me/theorems/67c48f5e-819e-4091-acec-501a5361afb3
-- title:
--   Pieces Counted: to Bits drop
-- statement:
--   The second half.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L86-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L86-L87

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

theorem PiecesCounted.toBits_drop {n : ℕ} (x y : Pieces.Bits n) : toBits n ((bitsOf x ++ bitsOf y).drop n) = y := by sorry
