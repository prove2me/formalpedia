-- Prove2me | Theorems.Thm_WidthK_ProgMain_mem_toFin
-- name    : WidthK.ProgMain.mem_toFin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:35:22.381974+00:00
-- url     : https://prove2.me/theorems/a9a5fccd-bf58-4a47-a923-56789eefb6ec
-- title:
--   Prog Main: mem to Fin
-- statement:
--   The members of `toFin s` are the clauses of s, read as sets.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L30-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L30-L31

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

theorem WidthK.ProgMain.mem_toFin {s : PFml} {X : Finset PLit} : X ∈ toFin s ↔ ∃ C ∈ s, C.toFinset = X := by sorry
