-- Prove2me | Theorems.Thm_PaddedDescent_decidesTM_of_padded
-- name    : PaddedDescent.decidesTM_of_padded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:15:29.834904+00:00
-- url     : https://prove2.me/theorems/ea48f817-f6f1-46eb-b251-aaa7ba450cd2
-- title:
--   Padded Descent: decides TM of padded
-- statement:
--   The same for 3-SAT. Let `e` and `A` be polynomial-time. There are a Turing machine `N` with
--   finite alphabets and a number `q`,
--   depending on `e` and `A` only, such that for every function `E` of the number n of variables: if on
--   the code x of every instance of
--   3-SAT e x ≤ E n, and A (x, the list of 2^(e x) units) is the bit «satisfiable», then `N` decides
--   3-SAT within
--   q · (25 (n + 2)^4 + 2^(E n))^q steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Pad.lean#L134-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Pad.lean#L134-L148

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_PaddedDescent_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_PaddedDescent_Pad
set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}

theorem PaddedDescent.decidesTM_of_padded (he : PolyT e) (hA : PolyT A) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ E : ℕ → ℕ,
        (∀ (n : ℕ) (φ : CNF n), Is3CNF φ →
          e (enc φ) ≤ E n ∧ (A (enc φ, pad (e (enc φ))) = true ↔ Satisfiable φ)) →
        DecidesTM N fun n => q * (25 * (n + 2) ^ 4 + 2 ^ E n) ^ q := by sorry
