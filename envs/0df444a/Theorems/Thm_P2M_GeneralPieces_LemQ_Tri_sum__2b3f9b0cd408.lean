-- Prove2me | Theorems.Thm_P2M_GeneralPieces_LemQ_Tri_sum__2b3f9b0cd408
-- name    : P2M_GeneralPieces_LemQ_Tri_sum__2b3f9b0cd408
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:21:00.844094+00:00
-- url     : https://prove2.me/theorems/eaea6bed-5377-49c3-a882-ed6a014983bc
-- title:
--   P2 M General Pieces Lem Q Tri sum  2b3f9b0cd408: P2 M General Pieces Lem Q Tri sum  2b3f9b0cd408
-- statement:
--   The P2 M General Pieces Lem Q Tri sum  2b3f9b0cd408 construction uses the P2 M General Pieces Lem Q Tri sum  2b3f9b0cd408 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L165-L169
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L165-L169

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

theorem P2M_GeneralPieces_LemQ_Tri_sum__2b3f9b0cd408 (hT : Tri T) (S : Finset Ptn) (q : Ptn → ℚ) (a b : V) : T a b (∑ μ ∈ S, q μ • tpow μ) = ∑ μ ∈ S, q μ • T a b (tpow μ) := by sorry

alias «GeneralPieces».«LemQ».«Tri».«sum₃» := P2M_GeneralPieces_LemQ_Tri_sum__2b3f9b0cd408
