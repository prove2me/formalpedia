-- Prove2me | Theorems.Thm_UniformInK_Thresholds_mul_betaSU_le
-- name    : UniformInK.Thresholds.mul_betaSU_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:42:00.967629+00:00
-- url     : https://prove2.me/theorems/6865859d-1e8a-4498-af7b-4a144dd00cb3
-- title:
--   Thresholds: mul beta SU le
-- statement:
--   τ·β r ≤ θ r.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Thresholds.lean#L33-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Thresholds.lean#L33-L36

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

theorem UniformInK.Thresholds.mul_betaSU_le (τ r : ℕ) : τ * betaSU τ r ≤ thetaU τ r := by sorry
