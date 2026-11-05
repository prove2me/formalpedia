-- Prove2me | Theorems.Thm_P2M_Eight_Level_netOf__col_8a246f415134
-- name    : P2M_Eight_Level_netOf__col_8a246f415134
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:58:18.602181+00:00
-- url     : https://prove2.me/theorems/6d4b9fba-2efa-4389-8b1a-83a14e34a1fb
-- title:
--   P2 M Eight Level net Of  col 8a246f415134: P2 M Eight Level net Of  col 8a246f415134
-- statement:
--   **The column network that the algorithm runs** is the column network of the proof of Proposition
--   3 (`Eight.colNetwork`), with settings and indices written as words.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L81-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L81-L83

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

theorem P2M_Eight_Level_netOf__col_8a246f415134 (g lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    netOfι g true lam y Rm = (colNetwork (gridR0 g g lam Rm) (digOf g lam y)).pull (fun _ => g * (g * g) * lam) (fun _ => stC g g true lam)
      (gridCl eightF [] g g true 0 lam y (gridR g g true lam Rm)) := by sorry

alias «Eight».«Level».«netOfι_col» := P2M_Eight_Level_netOf__col_8a246f415134
