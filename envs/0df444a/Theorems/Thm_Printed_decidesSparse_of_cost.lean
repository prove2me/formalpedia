-- Prove2me | Theorems.Thm_Printed_decidesSparse_of_cost
-- name    : Printed.decidesSparse_of_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:12:57.764206+00:00
-- url     : https://prove2.me/theorems/49875025-f927-4b0b-84e8-8bf0dcd837f6
-- title:
--   Printed: decides Sparse of cost
-- statement:
--   Since Φ is satisfiable if and only if Z > 0: a machine that counts within A·2^{δ'm} steps does
--   what the deciding form of the paper's reduction asks: decide whether a 3-CNF Φ with m ≤ Mn clauses
--   is satisfiable, in time O(2^{δ'm}) plus a polynomial in n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Proof.lean#L35-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Proof.lean#L35-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Proof
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Printed
open Groundwork Groundwork.Prog Eight Eight.SecNetworks Paper QueryMachines

theorem Printed.decidesSparse_of_cost {δ' : ℝ} {M A : ℕ} {Mc : StepMachine Formula ℤ}
    (h : ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ T : ℕ, Mc.Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length)) :
    Suffices.DecidesSparse δ' M Mc A := by sorry
