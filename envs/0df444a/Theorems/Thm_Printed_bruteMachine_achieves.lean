-- Prove2me | Theorems.Thm_Printed_bruteMachine_achieves
-- name    : Printed.bruteMachine_achieves
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:57:41.44509+00:00
-- url     : https://prove2.me/theorems/9c8509a8-5d50-4407-a097-9ce3ef16ac84
-- title:
--   Printed: brute Machine achieves
-- statement:
--   «Trying all 2^{λK(K−1)/2} choices of one string per edge»: brute force does what Definition 4
--   asks for (K, ½).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Achievable.lean#L83-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Achievable.lean#L83-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Absorb
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic
import Definitions.Def_Printed_Achievable
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines

theorem Printed.bruteMachine_achieves (K : ℕ) (hK : 2 ≤ K) : ∃ Cc : ℕ, AchievedBy (bruteMachine K) Cc K (1 / 2) := by sorry
