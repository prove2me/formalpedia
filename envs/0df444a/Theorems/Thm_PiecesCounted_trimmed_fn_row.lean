-- Prove2me | Theorems.Thm_PiecesCounted_trimmed_fn_row
-- name    : PiecesCounted.trimmed_fn_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:21:14.596356+00:00
-- url     : https://prove2.me/theorems/ac2fbd42-5a25-429a-88be-624ef6de93ac
-- title:
--   Pieces Counted: trimmed fn row
-- statement:
--   The function of the second pair in the new factorization, as a function of (x, y) and (u, v):
--   F(θ, z') = A_i(θ₁, θ₂, u, v).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L69-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L69-L70

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

theorem PiecesCounted.trimmed_fn_row {D : Data} {lam : ℕ} {i : ℤ} (hc : ¬ D.cap lam false i ≤ 2 * lam) (z : Pieces.Bits lam × Pieces.Bits lam) (θ : List Bool) :
    (trimmed D).fn lam false true i z θ = (D.fam lam).A i (toBits lam (θ.take lam)) (toBits lam (θ.drop lam)) z.1 z.2 := by sorry
