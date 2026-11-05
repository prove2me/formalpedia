-- Prove2me | Theorems.Thm_QueryMachines_Tower_Toy_val_child
-- name    : QueryMachines.Tower.Toy.val_child
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T22:02:44.174994+00:00
-- url     : https://prove2.me/theorems/bb3a7cc3-6767-487f-844a-ca86cd04d58c
-- title:
--   Toy: val child
-- statement:
--   The value of a callee is the sum over the strings that begin with its bit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Spec.lean#L47-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Spec.lean#L47-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Toy_Defs
import Definitions.Def_Tower_Toy_Spec
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower QueryMachines.Tower.Toy
open Groundwork

theorem QueryMachines.Tower.Toy.val_child (ℓ0 M0 l : ℕ) (b : Bool) (f : List Bool → Option ℕ) : (spec ℓ0 M0).val (l, b) ((spec ℓ0 M0).tab (l, b) f) = sumF l fun q => f (b :: q) := by sorry
