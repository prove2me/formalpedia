-- Prove2me | Theorems.Thm_QueryMachines_Tower_Toy_sumF_eq
-- name    : QueryMachines.Tower.Toy.sumF_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T22:03:09.425569+00:00
-- url     : https://prove2.me/theorems/25bf27d7-17f4-4056-bd3b-6b6eb171fc4f
-- title:
--   Toy: sum F eq
-- statement:
--   F(ℓ, f) is the sum of f over all bit strings of length ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Spec.lean#L23-L25
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Spec.lean#L23-L25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Toy_Defs
import Definitions.Def_Tower_Toy_Spec
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower QueryMachines.Tower.Toy
open Groundwork

theorem QueryMachines.Tower.Toy.sumF_eq : ∀ (l : ℕ) (f : List Bool → Option ℕ), sumF l f = ((words l).map fun q => (f q).getD 0).sum
  := by sorry
