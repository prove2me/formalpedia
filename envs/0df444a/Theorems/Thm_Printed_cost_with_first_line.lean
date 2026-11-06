-- Prove2me | Theorems.Thm_Printed_cost_with_first_line
-- name    : Printed.cost_with_first_line
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:07:06.657198+00:00
-- url     : https://prove2.me/theorems/b447a84b-f842-4c0a-8564-b8db2c4aec03
-- title:
--   Printed: cost with first line
-- statement:
--   **Line 6 of Algorithm 1** in front of a machine that counts: the bounds hold with A + 4 in the
--   place of A. On the formula without clauses the result 1 is the number of satisfying assignments of
--   no variables (`Eight.numSat_nil`), after one step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L173-L198
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L173-L198

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Count
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines

theorem Printed.cost_with_first_line {Mc : Stepped Formula ℤ} {δ' : ℝ} {A : ℕ}
    (h : ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ T : ℕ, Mc.Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length)) :
    ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ T : ℕ, (Stepped.ite (fun Φ : Formula => Φ.isEmpty) (Stepped.const 1) Mc).Runs Φ T ((A + 4) * size Φ ^ (A + 4)) (numSat Φ) ∧
      (T : ℝ) ≤ ((A + 4 : ℕ) : ℝ) * (2 : ℝ) ^ (δ' * Φ.length) := by sorry
