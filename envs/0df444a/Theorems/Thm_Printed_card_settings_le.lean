-- Prove2me | Theorems.Thm_Printed_card_settings_le
-- name    : Printed.card_settings_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:10:19.049181+00:00
-- url     : https://prove2.me/theorems/e0928377-40ec-4ab3-a597-10ad87bfd89d
-- title:
--   Printed: card settings le
-- statement:
--   «The sum defining W̃_γ(Θ) has at most (2^P)^{2g/K} = 2^{2gP/K} terms», with ⌊2g/K⌋, the largest
--   number of nodes that (G1) allows in a group.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L241-L252
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L241-L252

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
variable {C : Type} [HasSize C] {g K : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
omit [HasSize C]

theorem Printed.card_settings_le (h : N.Is P B) (hK0 : 0 < K) (x : ℕ) (γ : Fin K) (hG1 : K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) :
    #(tuples (fun a => Paper.grouping hK0 x a = γ) N.S []) ≤ 2 ^ (P * (2 * g / K)) := by sorry
