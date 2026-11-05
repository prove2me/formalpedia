-- Prove2me | Theorems.Thm_PiecesCounted_size_ints_le
-- name    : PiecesCounted.size_ints_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:59:26.197278+00:00
-- url     : https://prove2.me/theorems/012b36d3-c705-41e9-8b9c-e3e89c6797f1
-- title:
--   Pieces Counted: size ints le
-- statement:
--   A list of integers, each of size at most s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L58-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L58-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Basic
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Sizes
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog

theorem PiecesCounted.size_ints_le {l : List ℤ} {s : ℕ} (h : ∀ x ∈ l, size x ≤ s) : size l ≤ l.length * (s + 1) + 1 := by sorry
