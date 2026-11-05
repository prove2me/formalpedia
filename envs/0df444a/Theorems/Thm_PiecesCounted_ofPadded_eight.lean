-- Prove2me | Theorems.Thm_PiecesCounted_ofPadded_eight
-- name    : PiecesCounted.ofPadded_eight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:12:17.865056+00:00
-- url     : https://prove2.me/theorems/95d443c5-8810-49a9-8c0f-b874ff15fcab
-- title:
--   Pieces Counted: of Padded eight
-- statement:
--   The programs of these functions do not read the padding string: the data are the same for every
--   c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/EightSquare.lean#L33-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/EightSquare.lean#L33-L33

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

theorem PiecesCounted.ofPadded_eight (c : ℕ) : ofPadded Eight.eightF Eight.A c (fun _ => 0) = ofPadded Eight.eightF Eight.A 0 fun _ => 0 := by sorry
