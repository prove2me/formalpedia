-- Prove2me | Theorems.Thm_WidthK_SetAlg_mem_petals
-- name    : WidthK.SetAlg.mem_petals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:41:47.454396+00:00
-- url     : https://prove2.me/theorems/50e8f15b-600e-4bb4-9bf9-5af3041995ac
-- title:
--   Set Alg: mem petals
-- statement:
--   A petal is a clause of size j over H, without H.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L59-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L59-L60

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

theorem WidthK.SetAlg.mem_petals {F : Finset (Finset α)} {j : ℕ} {H D : Finset α} : D ∈ petals F j H ↔ ∃ C ∈ over F j H, C \ H = D := by sorry
