-- Prove2me | Theorems.Thm_Sat3_add_two_le_two_pow
-- name    : Sat3.add_two_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:24:01.091869+00:00
-- url     : https://prove2.me/theorems/895adbb0-a502-4ebc-9cd2-9379e56892ff
-- title:
--   Sat3: add two le two pow
-- statement:
--   m + 2 ≤ 2^(⌊log₂ m⌋ + 2), for every m (with `Nat.log2 0 = 0`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L51-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L51-L55

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

theorem Sat3.add_two_le_two_pow (m : ℕ) : m + 2 ≤ 2 ^ (Nat.log2 m + 2) := by sorry
