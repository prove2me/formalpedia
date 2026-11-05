-- Prove2me | Theorems.Thm_PiecesCounted_pow_two_mul_le
-- name    : PiecesCounted.pow_two_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:19:19.650655+00:00
-- url     : https://prove2.me/theorems/068bd064-acf6-42d6-a71e-aee558212e7f
-- title:
--   Pieces Counted: pow two mul le
-- statement:
--   (2λ)^c grows with c, for λ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Basic.lean#L37-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Basic.lean#L37-L38

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

theorem PiecesCounted.pow_two_mul_le {c c' lam : ℕ} (hl : 1 ≤ lam) (h : c ≤ c') : (2 * lam) ^ c ≤ (2 * lam) ^ c' := by sorry
