-- Prove2me | Theorems.Thm_PiecesCounted_trimmed_fn_first
-- name    : PiecesCounted.trimmed_fn_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:22:14.004947+00:00
-- url     : https://prove2.me/theorems/2c65e9dd-9849-4002-9149-00f474c46239
-- title:
--   Pieces Counted: trimmed fn first
-- statement:
--   The function of the first pair in the new factorization: [z = θ].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L64-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L64-L65

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

theorem PiecesCounted.trimmed_fn_first {D : Data} {lam : ℕ} {tr : Bool} {i : ℤ} (hc : ¬ D.cap lam tr i ≤ 2 * lam) (z : Pieces.Bits lam × Pieces.Bits lam) (θ : List Bool) :
    (trimmed D).fn lam tr false i z θ = if bitsOf z.1 ++ bitsOf z.2 = θ then 1 else 0 := by sorry
