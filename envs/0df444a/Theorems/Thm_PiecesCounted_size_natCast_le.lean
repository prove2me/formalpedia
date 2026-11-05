-- Prove2me | Theorems.Thm_PiecesCounted_size_natCast_le
-- name    : PiecesCounted.size_natCast_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:57:40.42994+00:00
-- url     : https://prove2.me/theorems/a8cb8ee5-105b-45c3-8435-797d40bbfc5b
-- title:
--   Pieces Counted: size nat Cast le
-- statement:
--   A natural number n, as an integer, has size at most n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L52-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L52-L55

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

theorem PiecesCounted.size_natCast_le (n : ℕ) : size (n : ℤ) ≤ n + 1 := by sorry
