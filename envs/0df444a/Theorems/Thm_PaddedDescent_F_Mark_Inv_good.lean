-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Inv_good
-- name    : PaddedDescent.F.Mark.Inv.good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:16:25.336202+00:00
-- url     : https://prove2.me/theorems/6a091a2f-945a-4ad8-8cf3-bd05a5e73a1c
-- title:
--   Inv: good
-- statement:
--   The invariant and a short last layer make the layers good.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L271-L274
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L271-L274

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

theorem PaddedDescent.F.Mark.Inv.good {n w : ℕ} : ∀ {Ls : List Fml}, Inv n w Ls → (Ls.getLastD []).length ≤ w → Good n w Ls
  := by sorry
