-- Prove2me | Theorems.Thm_P2M_GeneralPieces_Dual_sum_le_of_forall__d3e6cff7eb10
-- name    : P2M_GeneralPieces_Dual_sum_le_of_forall__d3e6cff7eb10
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:33.12176+00:00
-- url     : https://prove2.me/theorems/2060835e-ef06-44d1-8ed9-c1d61c553b1d
-- title:
--   P2 M General Pieces Dual sum le of forall  d3e6cff7eb10: P2 M General Pieces Dual sum le of forall  d3e6cff7eb10
-- statement:
--   The P2 M General Pieces Dual sum le of forall  d3e6cff7eb10 construction uses the P2 M General Pieces Dual sum le of forall  d3e6cff7eb10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L267-L271
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L267-L271

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

theorem P2M_GeneralPieces_Dual_sum_le_of_forall__d3e6cff7eb10 (μ : List ℕ+) (ks : List ℤ) (h : List.Forall₂ (fun (n : ℕ+) (k : ℤ) => (n : ℤ) ≤ k) μ ks) :
    (μ.map fun n : ℕ+ => (n : ℤ)).sum ≤ ks.sum := by sorry

alias «GeneralPieces».«Dual».«sum_le_of_forall₂» := P2M_GeneralPieces_Dual_sum_le_of_forall__d3e6cff7eb10
