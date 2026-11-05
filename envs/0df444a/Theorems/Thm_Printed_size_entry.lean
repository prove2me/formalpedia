-- Prove2me | Theorems.Thm_Printed_size_entry
-- name    : Printed.size_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:47:36.736392+00:00
-- url     : https://prove2.me/theorems/f1cbf442-71b3-4b9c-b8f9-6689461b6e8b
-- title:
--   Printed: size entry
-- statement:
--   An entry below 2^B has size at most B + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L174-L180
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L174-L180

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

theorem Printed.size_entry {v : ℤ} {B : ℕ} (h : |v| < 2 ^ B) : size v ≤ B + 1 := by sorry
