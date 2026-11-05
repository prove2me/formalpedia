-- Prove2me | Theorems.Thm_Sat3_not_ETH_TM_iff
-- name    : Sat3.not_ETH_TM_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:23:50.766267+00:00
-- url     : https://prove2.me/theorems/2ca018f9-b051-4da8-9acd-6c81a88c6055
-- title:
--   Sat3: not ETH TM iff
-- statement:
--   The negation of ETH_TM is «on Turing machines 3-SAT is in time O(2^{δn}) for every δ > 0».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EndLemmas.lean#L37-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EndLemmas.lean#L37-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_ToTuring_EndLemmas
set_option autoImplicit false
section
open Sat3
open Turing
open scoped NNReal ENNReal

theorem Sat3.not_ETH_TM_iff : ¬ETH_TM ↔ ∀ δ : ℝ≥0, 0 < δ → InTimeTM δ := by sorry
