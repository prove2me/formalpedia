-- Prove2me | Theorems.Thm_P2M_Eight_Level_netOf__row_07c080f825b3
-- name    : P2M_Eight_Level_netOf__row_07c080f825b3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:56:54.111623+00:00
-- url     : https://prove2.me/theorems/a37c697e-c2da-47b7-814e-8a92be1382b4
-- title:
--   P2 M Eight Level net Of  row 07c080f825b3: P2 M Eight Level net Of  row 07c080f825b3
-- statement:
--   **The row network that the algorithm runs** is the row network of the proof of Proposition 3
--   (`Eight.rowNetwork`), for the tables carried to the grid and the function ι written by y, with
--   settings and indices written as words: a setting of a row
--   in g · g² · λ bits (`stC`), an index θ of two rows in c_{a,a'} bits (`gridCl`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L75-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L75-L77

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

theorem P2M_Eight_Level_netOf__row_07c080f825b3 (g lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    netOfι g false lam y Rm = (rowNetwork (gridR0 g g lam Rm) (digOf g lam y)).pull (fun _ => g * (g * g) * lam) (fun _ => stC g g false lam)
      (gridCl eightF [] g g false 0 lam y (gridR g g false lam Rm)) := by sorry

alias «Eight».«Level».«netOfι_row» := P2M_Eight_Level_netOf__row_07c080f825b3
