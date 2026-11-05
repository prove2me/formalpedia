-- Prove2me | Theorems.Thm_P2M_Eight_Level_U_netOf__16d6ae6630a8
-- name    : P2M_Eight_Level_U_netOf__16d6ae6630a8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:19:01.096764+00:00
-- url     : https://prove2.me/theorems/828fa640-4d93-4cff-8c5e-1007db9cb2c4
-- title:
--   P2 M Eight Level U net Of  16d6ae6630a8: P2 M Eight Level U net Of  16d6ae6630a8
-- statement:
--   The number that the algorithm computes for a network (`totalG`) is its total U.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L131-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L131-L132

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_GridWords
import Theorems.Thm_Paper_mem_rectangles

set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}

theorem P2M_Eight_Level_U_netOf__16d6ae6630a8 (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    (netOfι g tr lam y Rm).U = totalG eightF g g tr 0 lam y := by sorry

alias «Eight».«Level».«U_netOfι» := P2M_Eight_Level_U_netOf__16d6ae6630a8
