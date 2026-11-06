-- Prove2me | Theorems.Thm_PiecesCounted_ite_cast_min
-- name    : PiecesCounted.ite_cast_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:01:11.568929+00:00
-- url     : https://prove2.me/theorems/60dca223-efdf-4c52-a47c-e0add099564a
-- title:
--   Pieces Counted: ite cast min
-- statement:
--   The smaller of two natural numbers, computed on integers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Assume.lean#L26-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Assume.lean#L26-L29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Trimmed
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Assume
set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.ite_cast_min (n m : ℕ) : (if (n : ℤ) ≤ (m : ℤ) then (n : ℤ) else (m : ℤ)) = ((min n m : ℕ) : ℤ) := by sorry
