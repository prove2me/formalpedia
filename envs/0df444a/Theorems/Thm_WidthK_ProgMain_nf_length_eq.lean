-- Prove2me | Theorems.Thm_WidthK_ProgMain_nf_length_eq
-- name    : WidthK.ProgMain.nf_length_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:37:29.844015+00:00
-- url     : https://prove2.me/theorems/0a7d4ba5-aa41-42d7-9a7c-34fa1a079210
-- title:
--   Prog Main: nf length eq
-- statement:
--   A formula in normal form has as many clauses as its set of clauses has members.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L71-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L71-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_ProgMain
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open WidthK WidthK.ProgMain
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem WidthK.ProgMain.nf_length_eq {s : PFml} (hs : NF s) : s.length = (toFin s).card := by sorry
