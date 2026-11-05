-- Prove2me | Theorems.Thm_PiecesCounted_assumeAlg_polyT
-- name    : PiecesCounted.assumeAlg_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:58:59.585197+00:00
-- url     : https://prove2.me/theorems/9d82d5f4-4c2d-40aa-a783-e92d8a6f30e0
-- title:
--   Pieces Counted: assume Alg poly T
-- statement:
--   The new algorithm has polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L166-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L166-L171

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_GeneralPieces_Trim_Prog
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Trimmed
set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.assumeAlg_polyT {Alg : Stepped (List Unit × Question) Answer} (h : Nonempty (IsPolyT Alg)) : Nonempty (IsPolyT (assumeAlg Alg)) := by sorry
