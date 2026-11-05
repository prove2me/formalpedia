-- Prove2me | Theorems.Thm_P2M_GeneralPieces_Dual_forall__replicate_53e3e372b2d2
-- name    : P2M_GeneralPieces_Dual_forall__replicate_53e3e372b2d2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:34:52.413753+00:00
-- url     : https://prove2.me/theorems/333439b7-a2c6-47f3-b0a1-f55d86017f95
-- title:
--   P2 M General Pieces Dual forall  replicate 53e3e372b2d2: P2 M General Pieces Dual forall  replicate 53e3e372b2d2
-- statement:
--   The P2 M General Pieces Dual forall  replicate 53e3e372b2d2 construction uses the P2 M General Pieces Dual forall  replicate 53e3e372b2d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L113-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L113-L120

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

theorem P2M_GeneralPieces_Dual_forall__replicate_53e3e372b2d2 {α : Type} (S : Finset α) (r : ℕ) (x : List α) :
    List.Forall₂ (fun a s => a ∈ s) x (List.replicate r S) ↔ x.length = r ∧ ∀ a ∈ x, a ∈ S := by sorry

alias «GeneralPieces».«Dual».«forall₂_replicate» := P2M_GeneralPieces_Dual_forall__replicate_53e3e372b2d2
