-- Prove2me | Theorems.Thm_P2M_GeneralPieces_PartA_y_succ_le__934cf0d43d5c
-- name    : P2M_GeneralPieces_PartA_y_succ_le__934cf0d43d5c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:18.251725+00:00
-- url     : https://prove2.me/theorems/ce06c079-6839-46eb-93cb-b792f6c7e31d
-- title:
--   P2 M General Pieces Part A y succ le  934cf0d43d5c: P2 M General Pieces Part A y succ le  934cf0d43d5c
-- statement:
--   The two together: y_{ℓ+1} ≤ (1 + 2^{−ℓ−2})·y_ℓ + 6·2^{ℓ−18(ℓ+1)}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L146-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L146-L151

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen

theorem P2M_GeneralPieces_PartA_y_succ_le__934cf0d43d5c (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) :
    y ρ x₀ (l + 1) ≤ (1 + 1 / 2 ^ (l + 2)) * y ρ x₀ l + 6 * 2 ^ l / 2 ^ (18 * (l + 1)) := by sorry

alias «GeneralPieces».«PartA».«y_succ_le'» := P2M_GeneralPieces_PartA_y_succ_le__934cf0d43d5c
