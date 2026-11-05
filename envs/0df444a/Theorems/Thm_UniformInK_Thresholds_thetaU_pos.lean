-- Prove2me | Theorems.Thm_UniformInK_Thresholds_thetaU_pos
-- name    : UniformInK.Thresholds.thetaU_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:41:50.458345+00:00
-- url     : https://prove2.me/theorems/0db02662-d87a-4581-ba6d-9bdbe70d6359
-- title:
--   Thresholds: theta U pos
-- statement:
--   The thresholds are positive, if τ is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Thresholds.lean#L27-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Thresholds.lean#L27-L30

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

theorem UniformInK.Thresholds.thetaU_pos {τ : ℕ} (hτ : 0 < τ) (i : ℕ) : 0 < thetaU τ i := by sorry
