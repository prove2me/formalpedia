-- Prove2me | Theorems.Thm_Sat3_log2_log2_le_sOf
-- name    : Sat3.log2_log2_le_sOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:24:14.679106+00:00
-- url     : https://prove2.me/theorems/3d0860f3-2508-4c8d-a189-e1bbe869c82c
-- title:
--   Sat3: log2 log2 le s Of
-- statement:
--   3·(⌊log₂⌊log₂ n⌋⌋ + 2) ≤ 19·(sOf n + 146) for every n, also where `sOf n = 0`. (Recall `sOf n` =
--   3·(⌊log₂⌊log₂ n⌋⌋ − 911)/19, rounded down.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L142-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L142-L144

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

theorem Sat3.log2_log2_le_sOf (n : ℕ) : 3 * (Nat.log2 (Nat.log2 n) + 2) ≤ 19 * (PaddedDescent.sOf n + 146) := by sorry
