-- Prove2me | Theorems.Thm_Printed_level_time_printed
-- name    : Printed.level_time_printed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:08:33.007263+00:00
-- url     : https://prove2.me/theorems/1e7e03be-37d2-4fc8-9566-f6f7b44c630c
-- title:
--   Printed: level time printed
-- statement:
--   «Cost», the number of steps, with the printed B₁ = gB + g²λ + 1 and the factor 3 of
--   `StOnProcedures`: from `Eight.Level.level_time` at B + gλ + 1 in the place of B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelCost.lean#L43-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelCost.lean#L43-L92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelNetworks
import Definitions.Def_Eight_ViaGrouping_Level
import Mathlib.Tactic
import Definitions.Def_Printed_LevelCost
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine

theorem Printed.level_time_printed (g K a C₁ : ℕ) {e : ℝ} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e) (Rn : ℕ) : ∃ A1 : ℕ, ∀ B lam : ℕ, 1 ≤ lam →
    (((tOf lam + 1) ^ Rn : ℕ) : ℝ) * ((((3 * C₁ : ℕ) : ℝ) + 1)
        * (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K)
        * (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * lam + 1 : ℕ) : ℝ)) ^ C₁ * ((a * (B + lam) ^ a : ℕ) : ℝ)) + 2
      ≤ (A1 : ℝ) * (2 : ℝ) ^ (((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * (lam : ℝ)) * ((B : ℝ) + lam) ^ A1 := by sorry
