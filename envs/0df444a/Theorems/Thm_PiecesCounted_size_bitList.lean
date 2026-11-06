-- Prove2me | Theorems.Thm_PiecesCounted_size_bitList
-- name    : PiecesCounted.size_bitList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:59:19.102053+00:00
-- url     : https://prove2.me/theorems/005b3e68-8038-48df-9b3f-d0cfb723c48e
-- title:
--   Pieces Counted: size bit List
-- statement:
--   A list of n bits has size 2n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L36-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L36-L41

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

theorem PiecesCounted.size_bitList (l : List Bool) : size l = 2 * l.length + 1 := by sorry
