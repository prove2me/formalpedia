-- Prove2me | Theorems.Thm_P2M_Coding_nodeG_lt__a7e270dc1ce1
-- name    : P2M_Coding_nodeG_lt__a7e270dc1ce1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:23:09.365449+00:00
-- url     : https://prove2.me/theorems/749fe93c-e1a4-4b4b-aa69-7b91e49b6392
-- title:
--   P2 M Coding node G lt  a7e270dc1ce1: P2 M Coding node G lt  a7e270dc1ce1
-- statement:
--   The position of the x-th grid point of a row or column is one of the g² positions.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L73-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L73-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_GridDefs
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_Eight_SecLevel_GridWords
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Grid
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Grid ClauseBound.Alg ClauseBound.Alg.GridNet Eight.SecNetworks Eight.ViaGrouping Eight.Level
variable {g : ℕ} {tr : Bool} {lam : ℕ}

theorem P2M_Coding_nodeG_lt__a7e270dc1ce1 (a : Fin (nParts g g tr)) {x : ℕ} (hx : x < g) : nodeG g tr a.val x < g * g := by sorry

alias «Coding».«nodeG_lt'» := P2M_Coding_nodeG_lt__a7e270dc1ce1
