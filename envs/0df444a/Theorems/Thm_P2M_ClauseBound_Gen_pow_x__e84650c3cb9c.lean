-- Prove2me | Theorems.Thm_P2M_ClauseBound_Gen_pow_x__e84650c3cb9c
-- name    : P2M_ClauseBound_Gen_pow_x__e84650c3cb9c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:10.958743+00:00
-- url     : https://prove2.me/theorems/317335b7-ef31-40ef-889a-d4d062ecc3c0
-- title:
--   P2 M Clause Bound Gen pow x  e84650c3cb9c: P2 M Clause Bound Gen pow x  e84650c3cb9c
-- statement:
--   2^10·(3x₀+6) ≤ 2^{x₀} for x₀ ≥ 18.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/PartA.lean#L51-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/PartA.lean#L51-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen
open Levels.Gen

theorem P2M_ClauseBound_Gen_pow_x__e84650c3cb9c (x₀ : ℕ) (hx : 18 ≤ x₀) : 2 ^ 10 * (3 * x₀ + 6) ≤ 2 ^ x₀ := by sorry

alias «ClauseBound».«Gen».«pow_x₀» := P2M_ClauseBound_Gen_pow_x__e84650c3cb9c
