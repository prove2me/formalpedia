-- Prove2me | Theorems.Thm_PiecesCounted_two_mul_le_pow
-- name    : PiecesCounted.two_mul_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:02:14.943577+00:00
-- url     : https://prove2.me/theorems/81f08c2c-4b8c-44a6-9651-a7a95310202a
-- title:
--   Pieces Counted: two mul le pow
-- statement:
--   2λ ≤ (2λ)^c for c ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L176-L176
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L176-L176

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Basic
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Sizes
set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog

theorem PiecesCounted.two_mul_le_pow {c : ℕ} (hc : 1 ≤ c) (lam : ℕ) : 2 * lam ≤ (2 * lam) ^ c := by sorry
