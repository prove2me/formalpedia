-- Prove2me | Theorems.Thm_PiecesCounted_oracle_value
-- name    : PiecesCounted.oracle_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:00:27.562952+00:00
-- url     : https://prove2.me/theorems/1157a6b5-d8dc-4597-bcae-12d725875999
-- title:
--   Pieces Counted: oracle value
-- statement:
--   The answer to the question for a value of A_i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L190-L193
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L190-L193

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

theorem PiecesCounted.oracle_value {D : Data} {u : List Unit} (hl : 1 ≤ u.length) {i : ℤ} (hi : i ∈ (D.fam u.length).I) {l1 l2 l3 l4 : List Bool} (e1 : l1.length = u.length) (e2 : l2.length = u.length)
    (e3 : l3.length = u.length) (e4 : l4.length = u.length) :
    D.oracle (u, .inr (.inr (.inr (.inl (i, l1, l2, l3, l4))))) = some (.inl ((D.fam u.length).A i (toBits _ l1) (toBits _ l2) (toBits _ l3) (toBits _ l4))) := by sorry
