-- Prove2me | Theorems.Thm_WidthK_ProgMain_sat_toFin
-- name    : WidthK.ProgMain.sat_toFin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:41:10.89242+00:00
-- url     : https://prove2.me/theorems/e6ff383c-b776-4eac-884d-182881511111
-- title:
--   Prog Main: sat to Fin
-- statement:
--   Truth values satisfy the set of clauses of x exactly if every clause of the list x has a true
--   literal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L88-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L88-L96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_ProgMain
set_option autoImplicit false
section
section
open WidthK WidthK.ProgMain
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}

theorem WidthK.ProgMain.sat_toFin (v : PLit → Prop) (x : PFml) : Sat v (toFin x) ↔ ∀ C ∈ x, ∃ a ∈ C, v a := by sorry
