-- Prove2me | Theorems.Thm_Printed_size_under
-- name    : Printed.size_under
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:05:58.792839+00:00
-- url     : https://prove2.me/theorems/d6cdad0d-e20f-43e6-a68b-d65ab933735a
-- title:
--   Printed: size under
-- statement:
--   The part of the states that comes from answering the queries by procedures, put under one
--   constant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L59-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L59-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Count
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines

theorem Printed.size_under (s P C₁ : ℕ) : s + C₁ * (P + 1) ^ C₁ + 4 ≤ (3 * C₁ + 5) * (s + P + 1) ^ (3 * C₁ + 5) := by sorry
