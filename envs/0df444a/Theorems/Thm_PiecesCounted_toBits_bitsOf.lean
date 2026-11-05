-- Prove2me | Theorems.Thm_PiecesCounted_toBits_bitsOf
-- name    : PiecesCounted.toBits_bitsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:21:34.350287+00:00
-- url     : https://prove2.me/theorems/299e8143-c845-4f35-9551-6a7f765b31c1
-- title:
--   Pieces Counted: to Bits bits Of
-- statement:
--   A string written as a list and read again.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L77-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L77-L79

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

theorem PiecesCounted.toBits_bitsOf {n : ℕ} (x : Pieces.Bits n) : toBits n (bitsOf x) = x := by sorry
