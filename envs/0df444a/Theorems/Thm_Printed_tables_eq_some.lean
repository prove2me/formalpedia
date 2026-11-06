-- Prove2me | Theorems.Thm_Printed_tables_eq_some
-- name    : Printed.tables_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:56:56.365508+00:00
-- url     : https://prove2.me/theorems/afe18ff1-3f59-4cc1-87d4-f694fa971104
-- title:
--   Printed: tables eq some
-- statement:
--   The tables answer only the queries of Definition 3, and with the entry.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Achievable.lean#L61-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Achievable.lean#L61-L68

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

theorem Printed.tables_eq_some {K lam : ℕ} {W : ℕ → List Bool → ℤ} {x : TableQuery} {v : ℤ} (h : tables K lam W x = some v) :
    x.1 < K ∧ x.2 ∈ words ((K - 1) * lam) ∧ v = W x.1 x.2 := by sorry
