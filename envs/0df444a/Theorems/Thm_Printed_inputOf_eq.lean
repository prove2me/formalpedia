-- Prove2me | Theorems.Thm_Printed_inputOf_eq
-- name    : Printed.inputOf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:50:31.419548+00:00
-- url     : https://prove2.me/theorems/51f839ca-6575-42c8-8ece-fcfbaba46eb7
-- title:
--   Printed: input Of eq
-- statement:
--   The input written down from numbers that agree with those of the network N is the input that
--   belongs to N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingProcs.lean#L38-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingProcs.lean#L38-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingProcs
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight Eight.SecNetworks QueryMachines QueryMachines.QueryMachine

theorem Printed.inputOf_eq {g : ℕ} (N : Net g) (P B : ℕ) (len : ℕ → ℕ) (cap : ℕ → ℕ → ℕ) (hl : ∀ a : Fin g, len a = N.len a) (hc : ∀ a b : Fin g, a ≠ b → cap a b = N.c a b) :
    inputOf g P B len cap = netInput N P B := by sorry
