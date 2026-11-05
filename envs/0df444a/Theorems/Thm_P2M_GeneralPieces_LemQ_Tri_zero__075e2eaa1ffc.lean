-- Prove2me | Theorems.Thm_P2M_GeneralPieces_LemQ_Tri_zero__075e2eaa1ffc
-- name    : P2M_GeneralPieces_LemQ_Tri_zero__075e2eaa1ffc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:20:40.479218+00:00
-- url     : https://prove2.me/theorems/496a7061-4964-4c98-8687-ffcd3de57981
-- title:
--   P2 M General Pieces Lem Q Tri zero  075e2eaa1ffc: P2 M General Pieces Lem Q Tri zero  075e2eaa1ffc
-- statement:
--   The P2 M General Pieces Lem Q Tri zero  075e2eaa1ffc construction uses the P2 M General Pieces Lem Q Tri zero  075e2eaa1ffc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L149-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L149-L151

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

theorem P2M_GeneralPieces_LemQ_Tri_zero__075e2eaa1ffc (hT : Tri T) (a b : V) : T a b 0 = 0 := by sorry

alias «GeneralPieces».«LemQ».«Tri».«zero₃» := P2M_GeneralPieces_LemQ_Tri_zero__075e2eaa1ffc
