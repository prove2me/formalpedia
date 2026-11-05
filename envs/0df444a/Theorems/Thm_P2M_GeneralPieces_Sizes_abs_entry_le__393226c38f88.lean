-- Prove2me | Theorems.Thm_P2M_GeneralPieces_Sizes_abs_entry_le__393226c38f88
-- name    : P2M_GeneralPieces_Sizes_abs_entry_le__393226c38f88
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:37:22.439431+00:00
-- url     : https://prove2.me/theorems/9d056aa0-f755-401c-8ee3-8f88a31711a1
-- title:
--   P2 M General Pieces Sizes abs entry le  393226c38f88: P2 M General Pieces Sizes abs entry le  393226c38f88
-- statement:
--   All entries of the tables of the monomials of weight at most h are at most 2^{12h²} in absolute
--   value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L207-L215
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L207-L215

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem P2M_GeneralPieces_Sizes_abs_entry_le__393226c38f88 {h : ℕ} (hh : 1 ≤ h) (a : List ℕ+) (ha : (toL a).sum ≤ h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |coef σ' (opMon a r (tpow σ))| ≤ 2 ^ (12 * h ^ 2) := by sorry

alias «GeneralPieces».«Sizes».«abs_entry_le'» := P2M_GeneralPieces_Sizes_abs_entry_le__393226c38f88
