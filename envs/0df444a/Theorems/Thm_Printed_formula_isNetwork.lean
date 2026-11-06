-- Prove2me | Theorems.Thm_Printed_formula_isNetwork
-- name    : Printed.formula_isNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:11:31.459866+00:00
-- url     : https://prove2.me/theorems/9feb13bc-2f43-418e-acc6-dbc1cc4fcaad
-- title:
--   Printed: formula is Network
-- statement:
--   The network of Φ, given by the procedures `formulaProcs`, is a network in the sense of
--   Definition 2 with parameters P = max{1, 2k·m̄}, B = 1, τ = 1. This is
--   `Eight.ViaGrouping.satNet_isNetworkP`; what is added is that the procedures hand over B = 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L40-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L40-L44

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

theorem Printed.formula_isNetwork {g : ℕ} (hg : 0 < g) (k : ℕ) (Φ : Fml) :
    SecNetworks.IsNetwork (formulaProcs g k) Φ (satNet g k Φ) (satPf g k Φ) 1 1 (size Φ + 2 * g + 6 * (mu g Φ * k) + 8 + 2) := by sorry
