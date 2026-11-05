-- Prove2me | Theorems.Thm_Sat3_logb_rpow_le_two_pow
-- name    : Sat3.logb_rpow_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:24:03.041818+00:00
-- url     : https://prove2.me/theorems/a2fae1e2-749e-4e09-b2f6-0719016f3358
-- title:
--   Sat3: logb rpow le two pow
-- statement:
--   If p·(⌊log₂⌊log₂ n⌋⌋ + 2) ≤ q·(s+b) then (log₂(n+2))^{p/q} ≤ 2^{s+b}: so 2^{-s} ≤ 2^b /
--   (log₂(n+2))^{p/q}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L73-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L73-L87

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

theorem Sat3.logb_rpow_le_two_pow {p q b s n : ℕ} (hq : 0 < q) (hs : p * (Nat.log2 (Nat.log2 n) + 2) ≤ q * (s + b)) :
    Real.logb 2 ((n : ℝ) + 2) ^ ((p : ℝ) / q) ≤ (2 : ℝ) ^ (s + b) := by sorry
