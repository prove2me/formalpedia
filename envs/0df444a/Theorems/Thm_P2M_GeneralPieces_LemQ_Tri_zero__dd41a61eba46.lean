-- Prove2me | Theorems.Thm_P2M_GeneralPieces_LemQ_Tri_zero__dd41a61eba46
-- name    : P2M_GeneralPieces_LemQ_Tri_zero__dd41a61eba46
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:20:37.62883+00:00
-- url     : https://prove2.me/theorems/eaa1a0fe-c259-4c0d-9d03-1bfe0a094857
-- title:
--   P2 M General Pieces Lem Q Tri zero  dd41a61eba46: P2 M General Pieces Lem Q Tri zero  dd41a61eba46
-- statement:
--   The P2 M General Pieces Lem Q Tri zero  dd41a61eba46 construction uses the P2 M General Pieces Lem Q Tri zero  dd41a61eba46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L145-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L145-L147

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
open GeneralPieces.LemQ.Tri
variable {T T' : V → V → V → V}

theorem P2M_GeneralPieces_LemQ_Tri_zero__dd41a61eba46 (hT : Tri T) (a f : V) : T a 0 f = 0 := by sorry

alias «GeneralPieces».«LemQ».«Tri».«zero₂» := P2M_GeneralPieces_LemQ_Tri_zero__dd41a61eba46
