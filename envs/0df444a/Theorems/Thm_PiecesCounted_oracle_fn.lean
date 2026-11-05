-- Prove2me | Theorems.Thm_PiecesCounted_oracle_fn
-- name    : PiecesCounted.oracle_fn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:01:17.437198+00:00
-- url     : https://prove2.me/theorems/a2a736b1-7b64-409f-9c26-3a67a3f72199
-- title:
--   Pieces Counted: oracle fn
-- statement:
--   The answer to the question for a value of a function of a factorization.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L196-L199
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L196-L199

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

theorem PiecesCounted.oracle_fn {D : Data} {u : List Unit} (hl : 1 ≤ u.length) {i : ℤ} (hi : i ∈ (D.fam u.length).I) {tr : Bool} (side : Bool) {l1 l2 θ : List Bool} (e1 : l1.length = u.length)
    (e2 : l2.length = u.length) (e3 : θ.length = D.cap u.length tr i) :
    D.oracle (u, .inr (.inr (.inr (.inr ((tr, side), i, l1, l2, θ))))) = some (.inl (D.fn u.length tr side i (toBits _ l1, toBits _ l2) θ)) := by sorry
