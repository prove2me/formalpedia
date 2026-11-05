-- Prove2me | Theorems.Thm_PiecesCounted_trimmed_is
-- name    : PiecesCounted.trimmed_is
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:21:50.020112+00:00
-- url     : https://prove2.me/theorems/232d02ca-dd40-45b7-801f-36f371bfb676
-- title:
--   Pieces Counted: trimmed is
-- statement:
--   The new data have clauses (a), (b) and the sizes of (c), with the same ρ and c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L95-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L95-L134

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

theorem PiecesCounted.trimmed_is {D : Data} {ρ : ℝ} {c : ℕ} (h : D.Is ρ c) : (trimmed D).Is ρ c := by sorry
