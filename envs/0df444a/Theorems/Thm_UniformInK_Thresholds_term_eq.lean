-- Prove2me | Theorems.Thm_UniformInK_Thresholds_term_eq
-- name    : UniformInK.Thresholds.term_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:42:49.994873+00:00
-- url     : https://prove2.me/theorems/f8c99d36-0793-43ce-b0d4-cc8c27ab3e0d
-- title:
--   Thresholds: term eq
-- statement:
--   One product in `ThrU.step`: 2·θ(i+1−j)·β(j+1) = 32·τ^(2i+1) for j ≤ i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Thresholds.lean#L39-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Thresholds.lean#L39-L44

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

theorem UniformInK.Thresholds.term_eq (τ : ℕ) {i j : ℕ} (hj : j ≤ i) : 2 * thetaU τ (i + 2 - (j + 1)) * betaSU τ (j + 1) = 32 * τ ^ (2 * i + 1) := by sorry
