-- Prove2me | Theorems.Thm_P2M_GeneralPieces_Dual_eq_of_forall__le_737cce703f30
-- name    : P2M_GeneralPieces_Dual_eq_of_forall__le_737cce703f30
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:31.471739+00:00
-- url     : https://prove2.me/theorems/6ae5a891-3d4b-46e6-af09-945d542f6a05
-- title:
--   P2 M General Pieces Dual eq of forall  le 737cce703f30: P2 M General Pieces Dual eq of forall  le 737cce703f30
-- statement:
--   «… hence k_i = μ_i, because both add up to h.»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L274-L283
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L274-L283

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem P2M_GeneralPieces_Dual_eq_of_forall__le_737cce703f30 (μ : List ℕ+) (ks : List ℤ) (h : List.Forall₂ (fun (n : ℕ+) (k : ℤ) => (n : ℤ) ≤ k) μ ks)
    (hs : ks.sum = (μ.map fun n : ℕ+ => (n : ℤ)).sum) : ks = μ.map fun n : ℕ+ => (n : ℤ) := by sorry

alias «GeneralPieces».«Dual».«eq_of_forall₂_le» := P2M_GeneralPieces_Dual_eq_of_forall__le_737cce703f30
