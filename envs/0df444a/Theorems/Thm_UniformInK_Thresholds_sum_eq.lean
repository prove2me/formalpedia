-- Prove2me | Theorems.Thm_UniformInK_Thresholds_sum_eq
-- name    : UniformInK.Thresholds.sum_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:42:27.542896+00:00
-- url     : https://prove2.me/theorems/b71df48a-5ae9-45f8-9e42-c8ed35be6a90
-- title:
--   Thresholds: sum eq
-- statement:
--   The sum in `ThrU.step` at i + 2 equals 32·(i+1)·τ^(2i+1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Thresholds.lean#L47-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Thresholds.lean#L47-L50

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

theorem UniformInK.Thresholds.sum_eq (τ i : ℕ) : ∑ i' ∈ range (i + 2), 2 * thetaU τ (i + 2 - i') * betaSU τ i' = 32 * (i + 1) * τ ^ (2 * i + 1) := by sorry
