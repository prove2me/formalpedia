-- Prove2me | Theorems.Thm_Sat3_rateBound_anti
-- name    : Sat3.rateBound_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:24:24.682678+00:00
-- url     : https://prove2.me/theorems/c2a7d504-5a48-44ff-b0cc-33f5a3054167
-- title:
--   Sat3: rate Bound anti
-- statement:
--   `rateBound` decreases when c grows.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L158-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L158-L164

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas
set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal

theorem Sat3.rateBound_anti (C : ℕ) {c c' : ℝ} (h : c' ≤ c) (n : ℕ) : rateBound C c n ≤ rateBound C c' n := by sorry
