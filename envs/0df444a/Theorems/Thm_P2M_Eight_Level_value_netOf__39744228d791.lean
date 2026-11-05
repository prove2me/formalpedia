-- Prove2me | Theorems.Thm_P2M_Eight_Level_value_netOf__39744228d791
-- name    : P2M_Eight_Level_value_netOf__39744228d791
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:10:50.296281+00:00
-- url     : https://prove2.me/theorems/775ca4c8-8c86-4874-9a97-61bf64da5296
-- title:
--   P2 M Eight Level value net Of  39744228d791: P2 M Eight Level value net Of  39744228d791
-- statement:
--   Both networks that the algorithm runs have the value Z_ι of display (34). From
--   `Eight.value_rowNetwork` and `Eight.value_colNetwork`: writing the settings as words does not change
--   the value, because every word of the right length writes a setting.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L103-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L103-L110

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

theorem P2M_Eight_Level_value_netOf__39744228d791 (hlam : 1 ≤ lam) (g : ℕ) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    (netOfι g tr lam y Rm).value = Zι (gridR0 g g lam Rm) (Eight.Level.patOf g lam y) := by sorry

alias «Eight».«Level».«value_netOfι» := P2M_Eight_Level_value_netOf__39744228d791
