-- Prove2me | Theorems.Thm_P2M_GeneralPieces_LemQ_Tri_sum__6d04f4d04421
-- name    : P2M_GeneralPieces_LemQ_Tri_sum__6d04f4d04421
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:21:10.088354+00:00
-- url     : https://prove2.me/theorems/e4d4b0fe-4c67-4832-8c87-ed55c1032b66
-- title:
--   P2 M General Pieces Lem Q Tri sum  6d04f4d04421: P2 M General Pieces Lem Q Tri sum  6d04f4d04421
-- statement:
--   The P2 M General Pieces Lem Q Tri sum  6d04f4d04421 construction uses the P2 M General Pieces Lem Q Tri sum  6d04f4d04421 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L159-L163
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L159-L163

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

theorem P2M_GeneralPieces_LemQ_Tri_sum__6d04f4d04421 (hT : Tri T) (S : Finset Ptn) (q : Ptn → ℚ) (a f : V) : T a (∑ μ ∈ S, q μ • tpow μ) f = ∑ μ ∈ S, q μ • T a (tpow μ) f := by sorry

alias «GeneralPieces».«LemQ».«Tri».«sum₂» := P2M_GeneralPieces_LemQ_Tri_sum__6d04f4d04421
