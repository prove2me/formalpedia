-- Prove2me | Theorems.Thm_PiecesCounted_toNat_shift
-- name    : PiecesCounted.toNat_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:02:39.00236+00:00
-- url     : https://prove2.me/theorems/084b0bfb-7f9e-46b0-b7ab-2acc58ff8b1e
-- title:
--   Pieces Counted: to Nat shift
-- statement:
--   The number of a piece in `P` from its number in the shifted index set.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/PaddedData.lean#L46-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/PaddedData.lean#L46-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_PaddedData
set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.toNat_shift (j : ℕ) (s : ℤ) : ((j : ℤ) + s - s).toNat = j := by sorry
