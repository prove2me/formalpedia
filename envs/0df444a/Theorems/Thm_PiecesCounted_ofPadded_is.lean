-- Prove2me | Theorems.Thm_PiecesCounted_ofPadded_is
-- name    : PiecesCounted.ofPadded_is
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:19:34.687861+00:00
-- url     : https://prove2.me/theorems/7638d2c9-8bab-40ea-a513-95a264218579
-- title:
--   Pieces Counted: of Padded is
-- statement:
--   The data made from pieces with a padding string have clauses (a), (b) and the sizes of (c), with
--   the same ρ and c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/PaddedData.lean#L58-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/PaddedData.lean#L58-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_PaddedData
set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.ofPadded_is {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} {shift : ℕ → ℤ} (h : AppRunningTime.IsPieces ρ c P A val)
    (hs : ∀ lam, 1 ≤ lam → |shift lam| + (2 * lam) ^ c < 2 ^ (2 * lam) ^ c) : (ofPadded P A c shift).Is ρ c := by sorry
