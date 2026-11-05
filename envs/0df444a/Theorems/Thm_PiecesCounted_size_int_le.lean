-- Prove2me | Theorems.Thm_PiecesCounted_size_int_le
-- name    : PiecesCounted.size_int_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:19:56.010045+00:00
-- url     : https://prove2.me/theorems/87014d55-8c6b-45de-9279-2cc3a7a2830b
-- title:
--   Pieces Counted: size int le
-- statement:
--   An integer below 2^X in absolute value has size at most X + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L44-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L44-L49

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

theorem PiecesCounted.size_int_le {z : ℤ} {X : ℕ} (h : |z| < 2 ^ X) : size z ≤ X + 1 := by sorry
