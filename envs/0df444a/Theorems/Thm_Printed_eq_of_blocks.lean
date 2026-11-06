-- Prove2me | Theorems.Thm_Printed_eq_of_blocks
-- name    : Printed.eq_of_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:50:20.799916+00:00
-- url     : https://prove2.me/theorems/1fa17af4-0c99-474c-955c-1f16f9d26092
-- title:
--   Printed: eq of blocks
-- statement:
--   Two strings of r·λ bits with the same r blocks of λ bits are equal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L101-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L101-L115

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

theorem Printed.eq_of_blocks (lam : ℕ) : ∀ (r : ℕ) (z z' : List Bool), z.length = r * lam → z'.length = r * lam → (∀ j < r, block lam j z = block lam j z') → z = z'
  := by sorry
