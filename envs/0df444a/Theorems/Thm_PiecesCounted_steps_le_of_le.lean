-- Prove2me | Theorems.Thm_PiecesCounted_steps_le_of_le
-- name    : PiecesCounted.steps_le_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:01:01.841006+00:00
-- url     : https://prove2.me/theorems/6764e1d6-e089-49e6-b3f2-c2f887886653
-- title:
--   Pieces Counted: steps le of le
-- statement:
--   2^{cλ} grows with c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Basic.lean#L29-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Basic.lean#L29-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Basic
set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.steps_le_of_le {c c' : ℕ} (lam : ℕ) (h : c ≤ c') : steps c lam ≤ steps c' lam := by sorry
