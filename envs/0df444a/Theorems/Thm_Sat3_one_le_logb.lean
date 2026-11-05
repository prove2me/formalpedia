-- Prove2me | Theorems.Thm_Sat3_one_le_logb
-- name    : Sat3.one_le_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:28:18.248329+00:00
-- url     : https://prove2.me/theorems/2b37e196-cab4-4aa4-8aac-40330d925dec
-- title:
--   Sat3: one le logb
-- statement:
--   log₂(n+2) ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L41-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L41-L44

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

theorem Sat3.one_le_logb (n : ℕ) : (1 : ℝ) ≤ Real.logb 2 ((n : ℝ) + 2) := by sorry
