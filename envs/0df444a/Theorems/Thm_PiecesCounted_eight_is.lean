-- Prove2me | Theorems.Thm_PiecesCounted_eight_is
-- name    : PiecesCounted.eight_is
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:41:55.484049+00:00
-- url     : https://prove2.me/theorems/60148c45-c403-4ef1-8845-d01d8a8ef501
-- title:
--   Pieces Counted: eight is
-- statement:
--   Clauses (a), (b) and the sizes of (c), for every c ≥ 8.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/EightSquare.lean#L48-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/EightSquare.lean#L48-L49

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

theorem PiecesCounted.eight_is {c : ℕ} (hc : 8 ≤ c) : (ofPadded Eight.eightF Eight.A 0 fun _ => 0).Is (11 / 12) c := by sorry
