-- Prove2me | Theorems.Thm_Sat3_le_rateBound_of_real
-- name    : Sat3.le_rateBound_of_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:24:03.699403+00:00
-- url     : https://prove2.me/theorems/4fcfbeaf-f304-4490-b6a5-e6c6c13f6b03
-- title:
--   Sat3: le rate Bound of real
-- statement:
--   The arithmetic core, for one n. Let s be tied to n by p·(⌊log₂⌊log₂ n⌋⌋ + 2) ≤ q·(s+b). Then a
--   number t of steps that is at most
--   A·2^{C₁·n/2^s + C₁} (real exponent) is at most C·2^{C·n/(log₂(n+2))^{p/q}} with C = A·2^{C₁} +
--   C₁·2^b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L95-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L95-L122

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

theorem Sat3.le_rateBound_of_real {p q b A C₁ s n t : ℕ} (hq : 0 < q) (hs : p * (Nat.log2 (Nat.log2 n) + 2) ≤ q * (s + b))
    (ht : (t : ℝ) ≤ A * (2 : ℝ) ^ ((C₁ : ℝ) * n / 2 ^ s + C₁)) :
    t ≤ rateBound (A * 2 ^ C₁ + C₁ * 2 ^ b) ((p : ℝ) / q) n := by sorry
