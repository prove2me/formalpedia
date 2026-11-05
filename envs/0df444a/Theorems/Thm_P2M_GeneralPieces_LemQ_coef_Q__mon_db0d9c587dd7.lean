-- Prove2me | Theorems.Thm_P2M_GeneralPieces_LemQ_coef_Q__mon_db0d9c587dd7
-- name    : P2M_GeneralPieces_LemQ_coef_Q__mon_db0d9c587dd7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:22:25.864864+00:00
-- url     : https://prove2.me/theorems/97ab1a6e-743e-46d0-ae80-0197e8ac8c26
-- title:
--   P2 M General Pieces Lem Q coef Q  mon db0d9c587dd7: P2 M General Pieces Lem Q coef Q  mon db0d9c587dd7
-- statement:
--   The same with the factors exchanged.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L324-L331
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L324-L331

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

theorem P2M_GeneralPieces_LemQ_coef_Q__mon_db0d9c587dd7 (hB : StBridge) (hOp : OpFacts) (h1 : O1) {h : ℕ} {μ ν : Ptn} (hμ : wt μ ≤ h) (hν : wt ν = h) (s : ℤ) (π σ : Ptn) :
    coef π (Q' h s (tpow μ) (tpow ν) (tpow σ)) = (ClauseBound.Boson.Qk' [((1 : ℤ), lst μ)] (lst ν) s (toN π) (toN σ) : ℚ) := by sorry

alias «GeneralPieces».«LemQ».«coef_Q'_mon» := P2M_GeneralPieces_LemQ_coef_Q__mon_db0d9c587dd7
