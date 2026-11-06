-- Prove2me | Theorems.Thm_UniformInK_Thresholds_step_le
-- name    : UniformInK.Thresholds.step_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:42:57.629528+00:00
-- url     : https://prove2.me/theorems/d6314a73-da02-4288-b08d-4f9dc06bdd15
-- title:
--   Thresholds: step le
-- statement:
--   `ThrU.step` for the thresholds `thetaU τ` and the bounds `betaSU τ`, if 8i ≤ τ + 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Thresholds.lean#L53-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Thresholds.lean#L53-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Spars_Thresholds
set_option autoImplicit false
section
section
open UniformInK
open Finset
open UniformInK.Thresholds

theorem UniformInK.Thresholds.step_le {τ i : ℕ} (hi : 0 < i) (hτ : 8 * i ≤ τ + 4) :
    4 * thetaU τ (i - 1) + ∑ i' ∈ range i, 2 * thetaU τ (i - i') * betaSU τ i' ≤ betaSU τ i := by sorry
