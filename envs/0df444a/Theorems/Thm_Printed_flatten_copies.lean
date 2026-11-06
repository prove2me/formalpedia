-- Prove2me | Theorems.Thm_Printed_flatten_copies
-- name    : Printed.flatten_copies
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:49:36.615504+00:00
-- url     : https://prove2.me/theorems/8858b6ad-d7a7-45fb-be17-d43dfc360f0a
-- title:
--   Printed: flatten copies
-- statement:
--   Definition 3, «encoded by concatenating its K − 1 strings»: the copies of a string of (K − 1)λ
--   bits, concatenated, give the string back.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L119-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L119-L128

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_CodingDefs
import Definitions.Def_QueryMachines_Comb
import Definitions.Def_Eight_SecNetworks_Clique
import Definitions.Def_Value_Clique
import Mathlib.Tactic
import Definitions.Def_Printed_Coding
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
variable {K lam : ℕ}

theorem Printed.flatten_copies (w : Fin K) {z : List Bool} (hz : z.length = (K - 1) * lam) :
    (List.ofFn fun u : Fin K => if u = w then [] else copyAt lam w u z).flatten = z := by sorry
