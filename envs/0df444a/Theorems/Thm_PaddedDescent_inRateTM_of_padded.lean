-- Prove2me | Theorems.Thm_PaddedDescent_inRateTM_of_padded
-- name    : PaddedDescent.inRateTM_of_padded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:15:47.640428+00:00
-- url     : https://prove2.me/theorems/df98b80f-f634-4c56-b83e-b874dcdea44e
-- title:
--   Padded Descent: in Rate TM of padded
-- statement:
--   Let `e` (from bit strings to numbers) and `A` (from a bit string and a list of units to a bit)
--   be polynomial-time. If on the code x
--   of every instance of 3-SAT on n variables e x ≤ C₀ · (n / 2^(sOf n) + 1) (division rounded down),
--   and A (x, the list of 2^(e x) units) is
--   the bit «satisfiable», then one Turing machine decides 3-SAT within C·2^{C·n/(log₂(n+2))^{3/19}}
--   steps, for some constant C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/PadRate.lean#L116-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/PadRate.lean#L116-L122

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

theorem PaddedDescent.inRateTM_of_padded (he : PolyT e) (hA : PolyT A) (C₀ : ℕ)
    (h : ∀ (n : ℕ) (φ : CNF n), Is3CNF φ →
      e (enc φ) ≤ C₀ * (n / 2 ^ sOf n + 1) ∧ (A (enc φ, pad (e (enc φ))) = true ↔ Satisfiable φ)) : InRateTM (3 / 19) := by sorry
