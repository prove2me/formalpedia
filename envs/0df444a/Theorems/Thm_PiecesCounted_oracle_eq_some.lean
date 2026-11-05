-- Prove2me | Theorems.Thm_PiecesCounted_oracle_eq_some
-- name    : PiecesCounted.oracle_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:03:20.917506+00:00
-- url     : https://prove2.me/theorems/c7692fd6-1347-4af3-ba21-149b346d905d
-- title:
--   Pieces Counted: oracle eq some
-- statement:
--   The oracle answers only for λ ≥ 1, and then with the right answer.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Basic.lean#L52-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Basic.lean#L52-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Basic
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.oracle_eq_some {D : Data} {g : List Unit × Question} {a : Answer} (h : D.oracle g = some a) : 1 ≤ g.1.length ∧ D.answer g.1.length g.2 = some a := by sorry
