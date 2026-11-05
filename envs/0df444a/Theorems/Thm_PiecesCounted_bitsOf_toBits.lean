-- Prove2me | Theorems.Thm_PiecesCounted_bitsOf_toBits
-- name    : PiecesCounted.bitsOf_toBits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:20:15.593423+00:00
-- url     : https://prove2.me/theorems/c3d0520e-b9e0-49c7-bcc9-8fd57e9dba10
-- title:
--   Pieces Counted: bits Of to Bits
-- statement:
--   A list of bits of the right length, read as a string and written as a list again.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/PaddedData.lean#L29-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/PaddedData.lean#L29-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_PaddedData
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.bitsOf_toBits {n : ℕ} {l : List Bool} (h : l.length = n) : bitsOf (toBits n l) = l := by sorry
