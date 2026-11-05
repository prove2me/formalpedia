-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_perm_flatten_placeM
-- name    : PaddedDescent.F.Mark.perm_flatten_placeM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:28.36914+00:00
-- url     : https://prove2.me/theorems/e43f71cc-41b7-4c9b-9c28-e626f311b1ea
-- title:
--   Mark: perm flatten place M
-- statement:
--   After the placement of C the clauses of the layers are C and the clauses before, in some order.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L472-L480
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L472-L480

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
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers

theorem PaddedDescent.F.Mark.perm_flatten_placeM {n w : ℕ} (C : Cl) : ∀ {Ls : List Fml}, Ls ≠ [] → (placeM n w C Ls).flatten.Perm (C :: Ls.flatten)
  := by sorry
