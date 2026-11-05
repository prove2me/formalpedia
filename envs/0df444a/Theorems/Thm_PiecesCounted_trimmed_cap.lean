-- Prove2me | Theorems.Thm_PiecesCounted_trimmed_cap
-- name    : PiecesCounted.trimmed_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:04:33.407203+00:00
-- url     : https://prove2.me/theorems/cc9eedc8-35be-4b0f-a75b-9237dda946b3
-- title:
--   Pieces Counted: trimmed cap
-- statement:
--   The new numbers of bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L57-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L57-L57

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

theorem PiecesCounted.trimmed_cap (D : Data) (lam : ℕ) (tr : Bool) (i : ℤ) : (trimmed D).cap lam tr i = min (D.cap lam tr i) (2 * lam) := by sorry
