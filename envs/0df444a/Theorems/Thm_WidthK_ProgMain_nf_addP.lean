-- Prove2me | Theorems.Thm_WidthK_ProgMain_nf_addP
-- name    : WidthK.ProgMain.nf_addP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:43:30.161119+00:00
-- url     : https://prove2.me/theorems/48f3d01d-937c-469b-ab9d-cb727846a565
-- title:
--   Prog Main: nf add P
-- statement:
--   `addP` keeps the normal form.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L55-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L55-L68

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

theorem WidthK.ProgMain.nf_addP {A s : PFml} (hA : NF A) (hs : NF s) : NF (addP A s) := by sorry
