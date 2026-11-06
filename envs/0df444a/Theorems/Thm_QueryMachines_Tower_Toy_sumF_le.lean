-- Prove2me | Theorems.Thm_QueryMachines_Tower_Toy_sumF_le
-- name    : QueryMachines.Tower.Toy.sumF_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:02:27.22531+00:00
-- url     : https://prove2.me/theorems/d451be4c-1a9c-4c40-9469-6e02e07a2c46
-- title:
--   Toy: sum F le
-- statement:
--   F(ℓ, f) is at most 2^ℓ times a bound on the entries.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Spec.lean#L35-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Spec.lean#L35-L44

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

theorem QueryMachines.Tower.Toy.sumF_le (M0 : ℕ) : ∀ (l : ℕ) (f : List Bool → Option ℕ), (∀ q, q.length = l → ∃ a, a ≤ M0 ∧ f q = some a) → sumF l f ≤ 2 ^ l * M0
  := by sorry
