-- Prove2me | Theorems.Thm_WidthK_ProgMain_card_litsBelow
-- name    : WidthK.ProgMain.card_litsBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:38:35.104953+00:00
-- url     : https://prove2.me/theorems/73ae8274-6ae4-4c28-9a76-a0b3f8936564
-- title:
--   Prog Main: card lits Below
-- statement:
--   There are at most 2n literals on variables below n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L203-L204
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L203-L204

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

theorem WidthK.ProgMain.card_litsBelow (n : ℕ) : (litsBelow n).card ≤ 2 * n := by sorry
