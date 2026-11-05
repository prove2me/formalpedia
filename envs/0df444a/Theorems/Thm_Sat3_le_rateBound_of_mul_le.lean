-- Prove2me | Theorems.Thm_Sat3_le_rateBound_of_mul_le
-- name    : Sat3.le_rateBound_of_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:24:06.370099+00:00
-- url     : https://prove2.me/theorems/709cf007-ecbd-44c8-9639-ed53a8c31113
-- title:
--   Sat3: le rate Bound of mul le
-- statement:
--   The same in natural numbers and without division: the exponent e satisfies e·2^s ≤ C₁·(n + 2^s),
--   that is e ≤ C₁·n/2^s + C₁.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L126-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L126-L138

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

theorem Sat3.le_rateBound_of_mul_le {p q b A C₁ s e n : ℕ} (hq : 0 < q)
    (hs : p * (Nat.log2 (Nat.log2 n) + 2) ≤ q * (s + b)) (he : e * 2 ^ s ≤ C₁ * (n + 2 ^ s)) :
    A * 2 ^ e ≤ rateBound (A * 2 ^ C₁ + C₁ * 2 ^ b) ((p : ℝ) / q) n := by sorry
