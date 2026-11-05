-- Prove2me | Theorems.Thm_P2M_Eight_colNetwork___9ff9d9772d4b
-- name    : P2M_Eight_colNetwork___9ff9d9772d4b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:06:01.104431+00:00
-- url     : https://prove2.me/theorems/f5b67313-dad0-43af-b4d8-341ff3302b44
-- title:
--   P2 M Eight col Network   9ff9d9772d4b: P2 M Eight col Network   9ff9d9772d4b
-- statement:
--   Ψ_{j,j'} in the column network: the product of the factors of the g straight edges between
--   columns j and j' and of A_{ι(q)}(x_q, y_q, u_q, v_q) over the rectangles q with these two columns.
--   «There x_q, u_q and y_q, v_q are separated.»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L97-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L97-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_GridDefs
import Definitions.Def_Eight_SecCrossing_LemPieces
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_Grid
import Theorems.Thm_Paper_card_rectangles
import Theorems.Thm_Paper_card_rectangles_le
import Theorems.Thm_Paper_mem_rectangles

set_option autoImplicit false
section
section
open Eight
open Finset Groundwork
open Paper (Rectangle rectangles mem_rectangles card_rectangles card_rectangles_le Settings RowSetting FactorsThrough)
variable {g lam : ℕ}

theorem P2M_Eight_colNetwork___9ff9d9772d4b (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) {ι : Rectangle g → ℕ} (hι : ∀ q, ι q ≤ tOf lam) {j j' : Fin g} (h : j < j')
    (z z' : RowSetting g lam) :
    (colNetwork W ι).Ψ j j' z z' = (∏ a, if z a (j', a) = z' a (j, a) then 1 else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2,
        Eight.A lam (ι (k, (j, j'))) (z k.1 (j', k.2)) (z' k.1 (j, k.2)) (z k.2 (j', k.1)) (z' k.2 (j, k.1)) := by sorry

alias «Eight».«colNetwork_Ψ» := P2M_Eight_colNetwork___9ff9d9772d4b
