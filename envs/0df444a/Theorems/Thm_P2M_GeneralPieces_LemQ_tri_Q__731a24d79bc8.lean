-- Prove2me | Theorems.Thm_P2M_GeneralPieces_LemQ_tri_Q__731a24d79bc8
-- name    : P2M_GeneralPieces_LemQ_tri_Q__731a24d79bc8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:21:50.066062+00:00
-- url     : https://prove2.me/theorems/7e452ae1-1e8d-43dc-a6b1-b296790e07f6
-- title:
--   P2 M General Pieces Lem Q tri Q  731a24d79bc8: P2 M General Pieces Lem Q tri Q  731a24d79bc8
-- statement:
--   The same with the factors exchanged.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L216-L216
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L216-L216

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem P2M_GeneralPieces_LemQ_tri_Q__731a24d79bc8 (hOp : OpFacts) (h : ℕ) (s : ℤ) : Tri (Q' h s) := by sorry

alias «GeneralPieces».«LemQ».«tri_Q'» := P2M_GeneralPieces_LemQ_tri_Q__731a24d79bc8
