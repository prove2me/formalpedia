-- Prove2me | Theorems.Thm_Printed_sum_lengths
-- name    : Printed.sum_lengths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:50:08.831681+00:00
-- url     : https://prove2.me/theorems/1ec8a63d-2260-47b7-82dc-1d1fc3b42b7a
-- title:
--   Printed: sum lengths
-- statement:
--   The first i of the K strings, of which the one at w is empty and the others have λ bits, have
--   i·λ bits together, or (i − 1)·λ if w is among them.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L34-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L34-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_CodingDefs
import Definitions.Def_QueryMachines_Comb
import Definitions.Def_Eight_SecNetworks_Clique
import Definitions.Def_Value_Clique
import Mathlib.Tactic
import Definitions.Def_Printed_Coding
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines

theorem Printed.sum_lengths (w lam i : ℕ) : ((List.range i).map fun u => if u = w then 0 else lam).sum = (if w < i then i - 1 else i) * lam := by sorry
