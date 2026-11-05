-- Prove2me | Theorems.Thm_WidthK_SetAlg_mem_over
-- name    : WidthK.SetAlg.mem_over
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:38:24.971077+00:00
-- url     : https://prove2.me/theorems/34457bdb-9bd2-4e34-92e4-818d846b5955
-- title:
--   Set Alg: mem over
-- statement:
--   The members of `over F i S`: the clauses of F of size i that contain S.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L55-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L55-L56

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

theorem WidthK.SetAlg.mem_over {F : Finset (Finset α)} {i : ℕ} {S C : Finset α} : C ∈ over F i S ↔ C ∈ F ∧ C.card = i ∧ S ⊆ C := by sorry
