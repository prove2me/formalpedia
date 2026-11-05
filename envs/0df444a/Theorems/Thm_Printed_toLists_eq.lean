-- Prove2me | Theorems.Thm_Printed_toLists_eq
-- name    : Printed.toLists_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:51:12.813104+00:00
-- url     : https://prove2.me/theorems/5fecff88-ac0f-4ef9-add7-18c29fba0b68
-- title:
--   Printed: to Lists eq
-- statement:
--   The query made from (w, z) in this development: the list of the function w' ↦ z_w(w').
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L131-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L131-L136

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_CodingDefs
import Definitions.Def_QueryMachines_Comb
import Definitions.Def_Eight_SecNetworks_Clique
import Definitions.Def_Value_Clique
import Mathlib.Tactic
import Definitions.Def_Printed_Coding
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
variable {K lam : ℕ}

theorem Printed.toLists_eq (lam : ℕ) (w : Fin K) (z : List Bool) :
    toLists K lam (w.val, z) = (w.val, List.ofFn fun u : Fin K => if u = w then [] else copyAt lam w u z) := by sorry
