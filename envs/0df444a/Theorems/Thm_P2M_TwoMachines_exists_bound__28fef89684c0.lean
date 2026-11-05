-- Prove2me | Theorems.Thm_P2M_TwoMachines_exists_bound__28fef89684c0
-- name    : P2M_TwoMachines_exists_bound__28fef89684c0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:50:09.403203+00:00
-- url     : https://prove2.me/theorems/5a000c0f-1f7f-4e5f-be57-5a8620e198bb
-- title:
--   P2 M Two Machines exists bound  28fef89684c0: P2 M Two Machines exists bound  28fef89684c0
-- statement:
--   The numbers: for all q₀, a₁, a₂, c₁, c₂ there is a q such that q₀·(t + 1)·(n + ((a₁·(p₁ + 1) +
--   a₁·t) + (a₂·(p₂ + 1) + a₂·t)) + 1)^q₀ ≤ q·(t + n + 1)^q whenever p₁ ≤ c₁·(3n + 3)^c₁ and p₂ ≤ c₂·(3n + 3)^c₂.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L163-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L163-L178

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_TwoMachines_Defs
import Definitions.Def_Wrap_CodingExists
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_TwoMachines_Main
set_option autoImplicit false
section
section
open TwoMachines
open Turing Groundwork Wrap CircuitLowerBound.Tab
variable {M₁ M₂ : TM2ComputableAux Bool Bool}

theorem P2M_TwoMachines_exists_bound__28fef89684c0 (q₀ a₁ a₂ c₁ c₂ : ℕ) : ∃ q : ℕ, ∀ t n p₁ p₂ : ℕ, p₁ ≤ c₁ * (3 * n + 2 + 1) ^ c₁ → p₂ ≤ c₂ * (3 * n + 2 + 1) ^ c₂ →
    q₀ * (t + 1) * (n + (a₁ * (p₁ + 1) + a₁ * t + (a₂ * (p₂ + 1) + a₂ * t)) + 1) ^ q₀ ≤ q * (t + n + 1) ^ q := by sorry

alias «TwoMachines».«exists_bound₂» := P2M_TwoMachines_exists_bound__28fef89684c0
