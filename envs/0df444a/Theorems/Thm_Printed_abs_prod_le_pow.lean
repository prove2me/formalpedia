-- Prove2me | Theorems.Thm_Printed_abs_prod_le_pow
-- name    : Printed.abs_prod_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:02:24.745852+00:00
-- url     : https://prove2.me/theorems/2a8c4c21-7290-4ac5-bd7e-3ee85c7d687b
-- title:
--   Printed: abs prod le pow
-- statement:
--   A product of n integers, each at most m in absolute value, is at most m^n in absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L195-L197
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L195-L197

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
import Theorems.Thm_ClauseBound_Grid_abs_prod_le_pow

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

theorem Printed.abs_prod_le_pow {ι : Type} (s : Finset ι) (f : ι → ℤ) (m : ℤ) (h : ∀ i ∈ s, |f i| ≤ m) : |∏ i ∈ s, f i| ≤ m ^ #s := by sorry
