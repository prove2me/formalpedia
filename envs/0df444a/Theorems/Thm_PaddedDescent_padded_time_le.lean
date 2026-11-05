-- Prove2me | Theorems.Thm_PaddedDescent_padded_time_le
-- name    : PaddedDescent.padded_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:15:20.796424+00:00
-- url     : https://prove2.me/theorems/1e27433f-43bf-436f-a852-492adff01cf0
-- title:
--   Padded Descent: padded time le
-- statement:
--   The arithmetic, for one n. Let 2^s ≤ ⌊log₂(n+2)⌋ and E·2^s ≤ C₀·(n + 2^s). Then the time
--   q·(25(n+2)^4 + 2^E)^q of the padded machine
--   is at most q·2^e' for e' = q·(E + 4·⌊log₂(n+2)⌋ + 10), and e'·2^s ≤ q·(C₀ + 42)·(n + 2^s).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/PadRate.lean#L64-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/PadRate.lean#L64-L92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_PaddedDescent_PadRate
set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing

theorem PaddedDescent.padded_time_le (q C₀ : ℕ) {n s E : ℕ} (hs : 2 ^ s ≤ Nat.log2 (n + 2)) (hE : E * 2 ^ s ≤ C₀ * (n + 2 ^ s)) :
    q * (25 * (n + 2) ^ 4 + 2 ^ E) ^ q ≤ q * 2 ^ (q * (E + 4 * Nat.log2 (n + 2) + 10)) ∧
      q * (E + 4 * Nat.log2 (n + 2) + 10) * 2 ^ s ≤ q * (C₀ + 42) * (n + 2 ^ s) := by sorry
