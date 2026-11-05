-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_placeM_eq_placeAt
-- name    : PaddedDescent.F.Mark.placeM_eq_placeAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:22.024818+00:00
-- url     : https://prove2.me/theorems/1958ea6d-0a92-4f0a-b0c7-11b2b8074092
-- title:
--   Mark: place M eq place At
-- statement:
--   The placement by recursion is the placement into the first layer whose test holds, or else the
--   last.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L348-L378
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L348-L378

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
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers

theorem PaddedDescent.F.Mark.placeM_eq_placeAt {n w : ℕ} (C : Cl) : ∀ {Ls : List Fml}, Ls ≠ [] → ∀ test : ℕ → Bool,
    (∀ i, i + 1 < Ls.length → (test i = true ↔ dropC n w C (Ls.getD i []) (Ls.drop (i + 1)))) →
    placeM n w C Ls = placeAt Ls C (((List.range (Ls.length - 1)).find? test).getD (Ls.length - 1))
  := by sorry
