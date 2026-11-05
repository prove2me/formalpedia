-- Prove2me | Theorems.Thm_UniformInK_Thresholds_betaSU_le
-- name    : UniformInK.Thresholds.betaSU_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:42:50.220648+00:00
-- url     : https://prove2.me/theorems/ce61f2e3-6096-48c0-8e3a-c2ed818ede41
-- title:
--   Thresholds: beta SU le
-- statement:
--   β k ≤ τ^(2k), if 2 ≤ τ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Thresholds.lean#L68-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Thresholds.lean#L68-L74

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

theorem UniformInK.Thresholds.betaSU_le {τ : ℕ} (hτ : 2 ≤ τ) (k : ℕ) : betaSU τ k ≤ τ ^ (2 * k) := by sorry
