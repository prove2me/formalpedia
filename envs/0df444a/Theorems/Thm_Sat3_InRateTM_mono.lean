-- Prove2me | Theorems.Thm_Sat3_InRateTM_mono
-- name    : Sat3.InRateTM.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:23:42.900276+00:00
-- url     : https://prove2.me/theorems/ecf1e72b-c9fc-408e-a5ef-fda4c1d3b263
-- title:
--   In Rate TM: mono
-- statement:
--   The claim for an exponent c implies the claim for every smaller exponent c'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L167-L169
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L167-L169

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono

set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal

theorem Sat3.InRateTM.mono {c c' : ℝ} (h : InRateTM c) (hc : c' ≤ c) : InRateTM c' := by sorry
