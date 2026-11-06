-- Prove2me | Theorems.Thm_Printed_level_size_printed
-- name    : Printed.level_size_printed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:08:50.671364+00:00
-- url     : https://prove2.me/theorems/316da60a-5f90-43fa-8f34-05fd5e2ead06
-- title:
--   Printed: level size printed
-- statement:
--   «Cost», the sizes: from `Eight.Level.level_size`; sc is the size of the pair (λ, B) in unary.
--   Not in the paper, which counts operations only.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelCost.lean#L96-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelCost.lean#L96-L117

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

theorem Printed.level_size_printed (g a C₁ Rn : ℕ) : ∃ A2 : ℕ, ∀ sc B lam M : ℕ, 1 ≤ lam → 1 ≤ g → M ≤ 2 * Rn * lam → sc ≤ 2 * (B + lam) + 2 →
    4 * sc + 3 * M + (g * (g ^ 3 * lam + (g * B + g ^ 2 * lam + 1)) + g * g * (g * B + g ^ 2 * lam + 1)) + B + size (g * g) + g * g * (2 * lam + 2) + 30
      + a * (sc + B + lam) ^ a + C₁ * (g ^ 3 * lam + (g * B + g ^ 2 * lam + 1)) ^ C₁ ≤ A2 * (B + lam) ^ A2 := by sorry
