-- Prove2me | Theorems.Thm_PaddedDescent_padM_reaches
-- name    : PaddedDescent.padM_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:14:39.285848+00:00
-- url     : https://prove2.me/theorems/80fcdc60-bc9a-41a2-a577-a7eb0d700224
-- title:
--   Padded Descent: pad M reaches
-- statement:
--   From the pad of length 2^k, k ≤ e x: the remaining doublings and the last step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Pad.lean#L68-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Pad.lean#L68-L88

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}

theorem PaddedDescent.padM_reaches (x : List Bool) : ∀ (d k : ℕ), k + d = e x →
    (padM e A).Reaches (2 * x.length + 2 * 2 ^ e x + 3) (A (x, pad (e x))) (.inl (x, pad k)) (d + 1)
  := by sorry
