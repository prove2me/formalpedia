-- Prove2me | Theorems.Thm_Sat3_SubexpTM_inTimeTM
-- name    : Sat3.SubexpTM.inTimeTM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:24:20.61047+00:00
-- url     : https://prove2.me/theorems/7eb805b4-7a8c-4527-a5df-20617ea70197
-- title:
--   Subexp TM: in Time TM
-- statement:
--   «2^{o(n)} with one machine» implies `InTimeTM δ` for every δ > 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L172-L175
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L172-L175

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

theorem Sat3.SubexpTM.inTimeTM (h : SubexpTM) {δ : ℝ≥0} (hδ : 0 < δ) : InTimeTM δ := by sorry
