-- Prove2me | Theorems.Thm_P2M_GeneralPieces_Rate_K2L_le__0b58532c6456
-- name    : P2M_GeneralPieces_Rate_K2L_le__0b58532c6456
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:33.79232+00:00
-- url     : https://prove2.me/theorems/f34c1295-b6bc-4edc-9bdd-e27a0bdbac7a
-- title:
--   P2 M General Pieces Rate K2 L le  0b58532c6456: P2 M General Pieces Rate K2 L le  0b58532c6456
-- statement:
--   The display "K²L ≤ U + 2ζN + K² ≤ (ρ + 3ζ)N + (c/4)g⁴·log(2λ) + K²"
--   (`GeneralPieces.Chain.K_sq_L_le`), with log Ξ in place of log(2λ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L169-L180
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L169-L180

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

theorem P2M_GeneralPieces_Rate_K2L_le__0b58532c6456 (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    (K x₀ l : ℝ) ^ 2 * lamNextG P (step P x₀ l) lam ≤ (ρ + 3 * zeta l) * ((g x₀ l : ℝ) ^ 4 * lam) +
      c / 4 * (g x₀ l : ℝ) ^ 4 * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) + (K x₀ l : ℝ) ^ 2 := by sorry

alias «GeneralPieces».«Rate».«K2L_le'» := P2M_GeneralPieces_Rate_K2L_le__0b58532c6456
