-- Prove2me | Theorems.Thm_Printed_achievable_of_eStar_lt
-- name    : Printed.achievable_of_eStar_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:58:23.638992+00:00
-- url     : https://prove2.me/theorems/2b6a3406-b18b-49fa-b886-4a4fc27fc4bd
-- title:
--   Printed: achievable of e Star lt
-- statement:
--   If e > e*, then (K, e) is achievable for infinitely many K.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Achievable.lean#L130-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Achievable.lean#L130-L133

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
import Theorems.Thm_Paper_achievable_of_eStar_lt

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines

theorem Printed.achievable_of_eStar_lt {e : ℝ} (he : eStar < e) (K₀ : ℕ) : ∃ K, K₀ ≤ K ∧ Achievable K e := by sorry
