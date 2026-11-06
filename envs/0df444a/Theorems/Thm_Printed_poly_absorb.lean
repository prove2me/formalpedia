-- Prove2me | Theorems.Thm_Printed_poly_absorb
-- name    : Printed.poly_absorb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:02:42.375766+00:00
-- url     : https://prove2.me/theorems/146b34de-0821-4129-8a9a-5f2fec953e37
-- title:
--   Printed: poly absorb
-- statement:
--   A polynomial in X ≤ 5Y is at most A'·Y^{A'}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelNetworks.lean#L41-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelNetworks.lean#L41-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_CodingDefs
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_GroupingProcs
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Mathlib.Tactic
import Definitions.Def_Printed_LevelNetworks
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine

theorem Printed.poly_absorb (A L : ℕ) : ∃ A' : ℕ, ∀ X Y : ℕ, 1 ≤ Y → X ≤ 5 * Y → A * X ^ A + L * X ≤ A' * Y ^ A' := by sorry
