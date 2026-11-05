-- Prove2me | Theorems.Thm_WidthK_ProgMain_toFin_addP
-- name    : WidthK.ProgMain.toFin_addP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:42:44.445761+00:00
-- url     : https://prove2.me/theorems/0c9cc94e-d6ba-4e53-ba11-27b619580975
-- title:
--   Prog Main: to Fin add P
-- statement:
--   As sets, `addP A s` consists of the clauses of A and the clauses of s that contain no clause of
--   A.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L39-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L39-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_ProgMain
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
section
open WidthK WidthK.ProgMain
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem WidthK.ProgMain.toFin_addP (A s : PFml) :
    toFin (addP A s) = toFin A ∪ (toFin s).filter fun C => ∀ D ∈ toFin A, ¬ D ⊆ C := by sorry
