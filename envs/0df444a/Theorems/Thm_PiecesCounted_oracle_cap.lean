-- Prove2me | Theorems.Thm_PiecesCounted_oracle_cap
-- name    : PiecesCounted.oracle_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:59:48.478327+00:00
-- url     : https://prove2.me/theorems/f2d1154c-25ae-404d-8903-0268ff8f3fbe
-- title:
--   Pieces Counted: oracle cap
-- statement:
--   The answer to the question for a number of bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L186-L187
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L186-L187

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_GeneralPieces_Trim_Prog
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Trimmed
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.oracle_cap {D : Data} {u : List Unit} (hl : 1 ≤ u.length) {i : ℤ} (hi : i ∈ (D.fam u.length).I) (tr : Bool) :
    D.oracle (u, .inr (.inr (.inl (tr, i)))) = some (.inl (D.cap u.length tr i)) := by sorry
