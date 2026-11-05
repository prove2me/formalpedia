-- Prove2me | Theorems.Thm_ThmVariables_cut_eq
-- name    : ThmVariables.cut_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:17:10.368358+00:00
-- url     : https://prove2.me/theorems/291a916b-ed42-42f0-9652-c832e5bac8d5
-- title:
--   Thm Variables: cut eq
-- statement:
--   min(a, b)/b = min(a/b, 1), for all natural numbers a and b (both sides are 0 if b = 0).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/PartA.lean#L38-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/PartA.lean#L38-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_ThmVariables_Bound
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ThmVariables_PartA
set_option autoImplicit false
section
section
open ThmVariables
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms
open Sat3 (CNF)

theorem ThmVariables.cut_eq (a b : ℕ) : ((min a b : ℕ) : ℝ) / (b : ℝ) = min ((a : ℝ) / b) 1 := by sorry
