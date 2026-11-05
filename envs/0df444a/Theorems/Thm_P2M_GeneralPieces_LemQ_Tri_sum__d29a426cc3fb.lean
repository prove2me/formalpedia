-- Prove2me | Theorems.Thm_P2M_GeneralPieces_LemQ_Tri_sum__d29a426cc3fb
-- name    : P2M_GeneralPieces_LemQ_Tri_sum__d29a426cc3fb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:21:03.971979+00:00
-- url     : https://prove2.me/theorems/c2505d8e-b11f-404a-902c-4c5f677d778a
-- title:
--   P2 M General Pieces Lem Q Tri sum  d29a426cc3fb: P2 M General Pieces Lem Q Tri sum  d29a426cc3fb
-- statement:
--   The P2 M General Pieces Lem Q Tri sum  d29a426cc3fb construction uses the P2 M General Pieces Lem Q Tri sum  d29a426cc3fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L153-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L153-L157

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

theorem P2M_GeneralPieces_LemQ_Tri_sum__d29a426cc3fb (hT : Tri T) (S : Finset Ptn) (q : Ptn → ℚ) (b f : V) : T (∑ μ ∈ S, q μ • tpow μ) b f = ∑ μ ∈ S, q μ • T (tpow μ) b f := by sorry

alias «GeneralPieces».«LemQ».«Tri».«sum₁» := P2M_GeneralPieces_LemQ_Tri_sum__d29a426cc3fb
