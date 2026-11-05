-- Prove2me | Theorems.Thm_PiecesCounted_sort_image_shift
-- name    : PiecesCounted.sort_image_shift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:57:50.525295+00:00
-- url     : https://prove2.me/theorems/dfae0700-9322-461a-80f1-fe86784dd79a
-- title:
--   Pieces Counted: sort image shift
-- statement:
--   {0, …, n − 1} shifted by s, in increasing order.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/PaddedData.lean#L38-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/PaddedData.lean#L38-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_PaddedData
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.sort_image_shift (n : ℕ) (s : ℤ) : ((range n).image fun i : ℕ => (i : ℤ) + s).sort = (List.range n).map fun i : ℕ => (i : ℤ) + s := by sorry
