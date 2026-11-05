-- Prove2me | Theorems.Thm_PiecesCounted_mem_ofPadded
-- name    : PiecesCounted.mem_ofPadded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:02:36.073866+00:00
-- url     : https://prove2.me/theorems/83f9f402-9090-40ae-9ca7-0d76a90efaec
-- title:
--   Pieces Counted: mem of Padded
-- statement:
--   The elements of the shifted index set.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/PaddedData.lean#L49-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/PaddedData.lean#L49-L52

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

theorem PiecesCounted.mem_ofPadded {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {c : ℕ} {shift : ℕ → ℤ} {lam : ℕ} {i : ℤ} (hi : i ∈ ((ofPadded P A c shift).fam lam).I) :
    ∃ j < P.cnt 0 lam, i = (j : ℤ) + shift lam := by sorry
