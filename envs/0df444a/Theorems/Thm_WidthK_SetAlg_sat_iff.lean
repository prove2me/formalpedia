-- Prove2me | Theorems.Thm_WidthK_SetAlg_sat_iff
-- name    : WidthK.SetAlg.sat_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:30:05.202769+00:00
-- url     : https://prove2.me/theorems/cd370cc0-ba90-473b-9395-d9f9187a6aaf
-- title:
--   Set Alg: sat iff
-- statement:
--   Truth values satisfy F exactly if they satisfy the light child or the heavy child. This holds
--   for all F, j and H.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L105-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L105-L122

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_SetAlg
set_option autoImplicit false
section
section
open WidthK WidthK.SetAlg
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {F : Finset (Finset α)} {j : ℕ} {H : Finset α}

theorem WidthK.SetAlg.sat_iff (v : α → Prop) : Sat v F ↔ Sat v (light F H) ∨ Sat v (heavy F j H) := by sorry
