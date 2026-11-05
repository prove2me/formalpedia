-- Prove2me | Theorems.Thm_P2M_GeneralPieces_Rate_B__le_18a470b66aae
-- name    : P2M_GeneralPieces_Rate_B__le_18a470b66aae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:32.873197+00:00
-- url     : https://prove2.me/theorems/2d0879a7-e0e6-42d2-8ba8-7190b9940040
-- title:
--   P2 M General Pieces Rate B  le 18a470b66aae: P2 M General Pieces Rate B  le 18a470b66aae
-- statement:
--   "Crude bounds give B' ≤ N + g²B₁", with B₁ = gB + g²(2λ)^c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L230-L237
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L230-L237

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}

theorem P2M_GeneralPieces_Rate_B__le_18a470b66aae (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    bNextG P (step P x₀ l) lam B ≤ g x₀ l ^ 4 * lam + g x₀ l ^ 2 * (g x₀ l * B + g x₀ l ^ 2 * (2 * lam) ^ c) := by sorry

alias «GeneralPieces».«Rate».«B'_le» := P2M_GeneralPieces_Rate_B__le_18a470b66aae
