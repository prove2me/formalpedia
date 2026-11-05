-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_placeE_eq_placeM
-- name    : PaddedDescent.F.Mark.placeE_eq_placeM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:34.489191+00:00
-- url     : https://prove2.me/theorems/b61f0722-03c7-4851-b9e0-328d357af725
-- title:
--   Mark: place E eq place M
-- statement:
--   With the invariant, a short last layer and exact evaluations, the placement by evaluations is
--   the placement by sums.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L451-L469
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L451-L469

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

theorem PaddedDescent.F.Mark.placeE_eq_placeM {n w : ℕ} {ev : List Fml → ℤ} {Ls : List Fml} (C : Cl) (h0 : Ls ≠ []) (hI : Inv n w Ls)
    (hl : (Ls.getLastD []).length ≤ w)
    (hev : ∀ i, i + 1 < Ls.length → ev (Ls.drop i) = trunc n w (Ls.drop i) ∧
      ev ((C :: Ls.getD i []) :: Ls.drop (i + 1)) = trunc n w ((C :: Ls.getD i []) :: Ls.drop (i + 1))) :
    placeE ev w Ls C = placeM n w C Ls := by sorry
