-- Prove2me | Theorems.Thm_Printed_card_factors_le
-- name    : Printed.card_factors_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:10:04.072626+00:00
-- url     : https://prove2.me/theorems/2c508364-8158-4bb6-8e17-c38a68f5e985
-- title:
--   Printed: card factors le
-- statement:
--   A term of the display has at most g² factors: one for each node of the group, one for each pair
--   of nodes of the group, one for each pair of a node of the group and a node outside.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L178-L192
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L178-L192

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

theorem Printed.card_factors_le {g K : ℕ} (χ : Fin g → Fin K) (γ : Fin K) :
    #{a | χ a = γ} + #{p ∈ pairs (Fin g) | χ p.1 = γ ∧ χ p.2 = γ} + #{p : Fin g × Fin g | χ p.1 = γ ∧ χ p.2 ≠ γ} ≤ g ^ 2 := by sorry
