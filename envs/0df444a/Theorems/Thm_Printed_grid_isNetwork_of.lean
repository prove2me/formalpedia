-- Prove2me | Theorems.Thm_Printed_grid_isNetwork_of
-- name    : Printed.grid_isNetwork_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:01:36.896023+00:00
-- url     : https://prove2.me/theorems/4defac12-237a-4244-842b-87b42ad2588c
-- title:
--   Printed: grid is Network of
-- statement:
--   **«Both networks satisfy Definition 2 with P = g³λ (so gP = N), with B₁ = gB + g²λ + 1 in the
--   role of B, and with τ = poly(B + λ)»** (proof of Proposition 3, «Two networks for each ι»), in the
--   form that the proof of Proposition 3 in this folder uses: Definition 2 is `SecNetworks.IsNetwork`
--   ((iii) as four step machines; B₁ is GIVEN by them), for the procedures `gridProcs` with the tables
--   of the clique on g² nodes built in: they give the network `levelNetP g tr λ y`, the printed B₁
--   included, within a·(B + λ)^a steps.
--   The context is (c, y), where c holds λ and B in unary. The hypothesis: «ask the tables», with the
--   tables built in, answers in one step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelNetworks.lean#L63-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelNetworks.lean#L63-L74

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine

theorem Printed.grid_isNetwork_of (hA : StAskServes) (g : ℕ) (hg : 1 ≤ g) : ∃ a : ℕ, ∀ (tr : Bool) (c : List Unit × List Unit) (lam B : ℕ) (W : ℕ → List Bool → ℤ) (y : ℕ), c.1.length = lam → c.2.length = B → 1 ≤ lam →
    (∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) → y < (tOf lam + 1) ^ nRect g →
    SecNetworks.IsNetwork ((gridProcs g tr).close (tables (g * g) lam W)) (c, y) (levelNetP g tr lam y (listTables (g * g) W)) (g ^ 3 * lam) (g * B + g ^ 2 * lam + 1) (a * (B + lam) ^ a)
      (size c + size (g * g) + g * g * (2 * lam + 2) + B + 3 + a * (size c + B + lam) ^ a + 2) := by sorry
