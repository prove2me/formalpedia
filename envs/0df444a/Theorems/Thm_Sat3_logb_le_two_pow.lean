-- Prove2me | Theorems.Thm_Sat3_logb_le_two_pow
-- name    : Sat3.logb_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:24:04.978074+00:00
-- url     : https://prove2.me/theorems/97d46540-9f91-4b9a-8a83-241ed2760581
-- title:
--   Sat3: logb le two pow
-- statement:
--   log₂(n+2) ≤ 2^(⌊log₂⌊log₂ n⌋⌋ + 2), for every n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L58-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L58-L69

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

theorem Sat3.logb_le_two_pow (n : ℕ) :
    Real.logb 2 ((n : ℝ) + 2) ≤ (2 : ℝ) ^ (Nat.log2 (Nat.log2 n) + 2) := by sorry
