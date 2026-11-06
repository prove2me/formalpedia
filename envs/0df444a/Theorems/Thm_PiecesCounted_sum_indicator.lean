-- Prove2me | Theorems.Thm_PiecesCounted_sum_indicator
-- name    : PiecesCounted.sum_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:58:35.36481+00:00
-- url     : https://prove2.me/theorems/ca32bfd7-49cf-4d03-b0d3-b7f1d20aeb9d
-- title:
--   Pieces Counted: sum indicator
-- statement:
--   F(z, z') = Σ_θ [z = θ]·F(θ, z'), over the strings θ of 2λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L90-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L90-L92

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

theorem PiecesCounted.sum_indicator {n : ℕ} (x y : Pieces.Bits n) (F : List Bool → ℤ) : ∑ θ ∈ words (2 * n), (if bitsOf x ++ bitsOf y = θ then 1 else 0) * F θ = F (bitsOf x ++ bitsOf y) := by sorry
