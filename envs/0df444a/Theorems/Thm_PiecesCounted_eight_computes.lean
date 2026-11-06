-- Prove2me | Theorems.Thm_PiecesCounted_eight_computes
-- name    : PiecesCounted.eight_computes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:12:20.740178+00:00
-- url     : https://prove2.me/theorems/4daf3deb-e455-4114-a0fb-3bb6d9432d48
-- title:
--   Pieces Counted: eight computes
-- statement:
--   The one algorithm, within 2^{cλ} operations for every c ≥ 8.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/EightSquare.lean#L52-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/EightSquare.lean#L52-L54

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

theorem PiecesCounted.eight_computes {c : ℕ} (hc : 8 ≤ c) : Computes (algOf Eight.eightF AppRunningTime.valEight 0 fun _ => 0) (ofPadded Eight.eightF Eight.A 0 fun _ => 0) c := by sorry
