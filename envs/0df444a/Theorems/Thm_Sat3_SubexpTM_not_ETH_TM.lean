-- Prove2me | Theorems.Thm_Sat3_SubexpTM_not_ETH_TM
-- name    : Sat3.SubexpTM.not_ETH_TM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:49.653673+00:00
-- url     : https://prove2.me/theorems/71303c67-f54c-407c-9693-e24b33e13438
-- title:
--   Subexp TM: not ETH TM
-- statement:
--   «2^{o(n)} with one machine» refutes the Exponential Time Hypothesis.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L178-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L178-L178

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

theorem Sat3.SubexpTM.not_ETH_TM (h : SubexpTM) : ¬ ETH_TM := by sorry
