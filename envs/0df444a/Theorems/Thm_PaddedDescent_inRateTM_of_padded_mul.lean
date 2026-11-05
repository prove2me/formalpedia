-- Prove2me | Theorems.Thm_PaddedDescent_inRateTM_of_padded_mul
-- name    : PaddedDescent.inRateTM_of_padded_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:15:34.446871+00:00
-- url     : https://prove2.me/theorems/d8bc3f92-7402-4fce-bdaf-2ba66313a006
-- title:
--   Padded Descent: in Rate TM of padded mul
-- statement:
--   Without division. Let `e` and `A` be polynomial-time, and let E be a function of the number n of
--   variables with
--   E n · 2^(sOf n) ≤ C₀ · (n + 2^(sOf n)), that is E n ≤ C₀·n/2^(sOf n) + C₀. If on the code x of every
--   instance of 3-SAT e x ≤ E n, and
--   A (x, the list of 2^(e x) units) is the bit «satisfiable», then the rate statement holds with c =
--   3/19.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/PadRate.lean#L102-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/PadRate.lean#L102-L108

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
variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}

theorem PaddedDescent.inRateTM_of_padded_mul (he : PolyT e) (hA : PolyT A) (C₀ : ℕ) (E : ℕ → ℕ)
    (hE : ∀ n, E n * 2 ^ sOf n ≤ C₀ * (n + 2 ^ sOf n))
    (h : ∀ (n : ℕ) (φ : CNF n), Is3CNF φ →
      e (enc φ) ≤ E n ∧ (A (enc φ, pad (e (enc φ))) = true ↔ Satisfiable φ)) : InRateTM (3 / 19) := by sorry
