-- Prove2me | Theorems.Thm_PaddedDescent_pad_bound
-- name    : PaddedDescent.pad_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:16:11.059149+00:00
-- url     : https://prove2.me/theorems/86a9b200-a288-45dd-b423-fe570305418d
-- title:
--   Padded Descent: pad bound
-- statement:
--   Arithmetic: the bound of the host for the padding machine is a polynomial in |x| + 2^e + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Pad.lean#L98-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Pad.lean#L98-L109

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

theorem PaddedDescent.pad_bound (q l e : ℕ) : q * (e + 1 + 1) * (l + (2 * l + 2 * 2 ^ e + 3) + 1) ^ q ≤
    (q * 4 ^ (q + 1) + (q + 1)) * (l + 2 ^ e + 1) ^ (q * 4 ^ (q + 1) + (q + 1)) := by sorry
