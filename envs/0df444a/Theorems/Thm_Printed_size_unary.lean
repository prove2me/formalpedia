-- Prove2me | Theorems.Thm_Printed_size_unary
-- name    : Printed.size_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:56:31.232813+00:00
-- url     : https://prove2.me/theorems/b06ef2b1-7588-4a46-868c-7b90afd5d4a0
-- title:
--   Printed: size unary
-- statement:
--   The number n in unary has size 2n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Achievable.lean#L53-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Achievable.lean#L53-L58

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

theorem Printed.size_unary (n : ℕ) : size (unary n) = 2 * n + 1 := by sorry
