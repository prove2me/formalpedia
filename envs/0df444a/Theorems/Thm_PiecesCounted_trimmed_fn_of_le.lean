-- Prove2me | Theorems.Thm_PiecesCounted_trimmed_fn_of_le
-- name    : PiecesCounted.trimmed_fn_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:22:25.086278+00:00
-- url     : https://prove2.me/theorems/1eaa9de8-ca9c-4d85-aac6-d6d85fa50f7b
-- title:
--   Pieces Counted: trimmed fn of le
-- statement:
--   A factorization through at most 2λ bits is kept.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L60-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L60-L61

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

theorem PiecesCounted.trimmed_fn_of_le {D : Data} {lam : ℕ} {tr : Bool} {i : ℤ} (hc : D.cap lam tr i ≤ 2 * lam) (side : Bool) (z : Pieces.Bits lam × Pieces.Bits lam) (θ : List Bool) :
    (trimmed D).fn lam tr side i z θ = D.fn lam tr side i z θ := by sorry
