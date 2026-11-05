-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_trunc_eq_XX
-- name    : PaddedDescent.F.Mark.trunc_eq_XX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:28.018686+00:00
-- url     : https://prove2.me/theorems/da5cc238-0dee-4907-9c15-45329c3b9386
-- title:
--   Mark: trunc eq XX
-- statement:
--   One evaluation on good layers, as a natural number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L311-L316
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L311-L316

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

theorem PaddedDescent.F.Mark.trunc_eq_XX {n w : ℕ} {Λ : Fml} {rest : List Fml} (h : Good n w (Λ :: rest)) : trunc n w (Λ :: rest) = (XX n Λ rest : ℤ) := by sorry
