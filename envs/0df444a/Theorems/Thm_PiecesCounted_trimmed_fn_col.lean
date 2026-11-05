-- Prove2me | Theorems.Thm_PiecesCounted_trimmed_fn_col
-- name    : PiecesCounted.trimmed_fn_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:21:31.001905+00:00
-- url     : https://prove2.me/theorems/4aa6da73-1df3-4572-bba2-5ac990512dfc
-- title:
--   Pieces Counted: trimmed fn col
-- statement:
--   The same as a function of (x, u) and (y, v): F(θ, z') = A_i(θ₁, y, θ₂, v).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L73-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L73-L74

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

theorem PiecesCounted.trimmed_fn_col {D : Data} {lam : ℕ} {i : ℤ} (hc : ¬ D.cap lam true i ≤ 2 * lam) (z : Pieces.Bits lam × Pieces.Bits lam) (θ : List Bool) :
    (trimmed D).fn lam true true i z θ = (D.fam lam).A i (toBits lam (θ.take lam)) z.1 (toBits lam (θ.drop lam)) z.2 := by sorry
