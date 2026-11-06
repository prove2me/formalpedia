-- Prove2me | Theorems.Thm_QueryMachines_Tower_Toy_sumF_congr
-- name    : QueryMachines.Tower.Toy.sumF_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:02:37.763363+00:00
-- url     : https://prove2.me/theorems/115fb397-3dca-4cb2-be2c-3125079ab05c
-- title:
--   Toy: sum F congr
-- statement:
--   F(ℓ, f) reads only the entries of the strings of length ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Spec.lean#L28-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Spec.lean#L28-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Toy_Defs
import Definitions.Def_Tower_Toy_Spec
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower QueryMachines.Tower.Toy
open Groundwork

theorem QueryMachines.Tower.Toy.sumF_congr : ∀ (l : ℕ) (f g : List Bool → Option ℕ), (∀ q, q.length = l → f q = g q) → sumF l f = sumF l g
  := by sorry
