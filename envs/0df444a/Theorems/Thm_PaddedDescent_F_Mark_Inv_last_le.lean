-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Inv_last_le
-- name    : PaddedDescent.F.Mark.Inv.last_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:46.065237+00:00
-- url     : https://prove2.me/theorems/85bb93af-9d7f-41e0-832b-988f5c7ae16b
-- title:
--   Inv: last le
-- statement:
--   The last of R + 1 layers holds at most (2/3)^R of all clauses, and 5 more.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L289-L306
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L289-L306

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkSums
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_PaddedDescent_F_MarkLayers
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers

theorem PaddedDescent.F.Mark.Inv.last_le {n w : ℕ} : ∀ {Ls : List Fml}, Inv n w Ls → Ls ≠ [] →
    3 ^ (Ls.length - 1) * (Ls.getLastD []).length + 5 * 2 ^ (Ls.length - 1) ≤ 2 ^ (Ls.length - 1) * Ls.flatten.length + 5 * 3 ^ (Ls.length - 1)
  := by sorry
