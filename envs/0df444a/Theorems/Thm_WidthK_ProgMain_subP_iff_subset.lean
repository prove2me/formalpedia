-- Prove2me | Theorems.Thm_WidthK_ProgMain_subP_iff_subset
-- name    : WidthK.ProgMain.subP_iff_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:43:01.036507+00:00
-- url     : https://prove2.me/theorems/9c2fde7e-fc14-4641-ad3d-a58321dfa6f6
-- title:
--   Prog Main: sub P iff subset
-- statement:
--   The test `subP D C` says that D, read as a set, is contained in C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L34-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L34-L35

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

theorem WidthK.ProgMain.subP_iff_subset (D C : PCl) : subP D C = true ↔ D.toFinset ⊆ C.toFinset := by sorry
