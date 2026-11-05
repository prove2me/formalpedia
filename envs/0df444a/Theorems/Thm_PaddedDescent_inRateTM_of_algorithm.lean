-- Prove2me | Theorems.Thm_PaddedDescent_inRateTM_of_algorithm
-- name    : PaddedDescent.inRateTM_of_algorithm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:17:02.668346+00:00
-- url     : https://prove2.me/theorems/235c62c9-3700-453d-ba9a-1d2fcbff325c
-- title:
--   Padded Descent: in Rate TM of algorithm
-- statement:
--   The reduction. Let 2^s₀ ≤ C₀ and let `A` be a polynomial-time function of a bit string and a
--   list of units. If for every n with
--   sOf n ≥ s₀ and every instance φ of 3-SAT on n variables A (code of φ, the list of 2^(C₀·(n / 2^(sOf
--   n) + 1)) units) is the bit «satisfiable»,
--   then one Turing machine decides 3-SAT within C·2^{C·n/(log₂(n+2))^{3/19}} steps, for some constant
--   C. The division rounds down.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Reduce.lean#L69-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Reduce.lean#L69-L85

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_PadRate
import Definitions.Def_PaddedDescent_BrutePad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_PaddedDescent_Reduce
set_option autoImplicit false
section
open PaddedDescent
open Groundwork Groundwork.Decode Sat3 Turing

theorem PaddedDescent.inRateTM_of_algorithm (C₀ s₀ : ℕ) (hC : 2 ^ s₀ ≤ C₀) {A : List Bool × List Unit → Bool} (hA : PolyT A)
    (h : ∀ (n : ℕ) (φ : CNF n), Is3CNF φ → s₀ ≤ sOf n → (A (enc φ, pad (padLog C₀ n)) = true ↔ Satisfiable φ)) :
    InRateTM (3 / 19) := by sorry
