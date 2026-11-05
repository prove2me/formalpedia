-- Prove2me | Theorems.Thm_P2M_Eight_rowNetwork___891e43b2654c
-- name    : P2M_Eight_rowNetwork___891e43b2654c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:05:56.487212+00:00
-- url     : https://prove2.me/theorems/11b28aad-442a-4b66-81ab-a9950e3fd415
-- title:
--   P2 M Eight row Network   891e43b2654c: P2 M Eight row Network   891e43b2654c
-- statement:
--   «Ψ_{a,a'} is the product of the factors of the g straight edges between rows a and a' and of
--   A_{ι(q)}(x_q, y_q, u_q, v_q) over the g(g−1)/2 rectangles q with these two rows.» Same as in the
--   paper.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L87-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L87-L92

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

theorem P2M_Eight_rowNetwork___891e43b2654c (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) {ι : Rectangle g → ℕ} (hι : ∀ q, ι q ≤ tOf lam) {a a' : Fin g} (h : a < a')
    (z z' : RowSetting g lam) :
    (rowNetwork W ι).Ψ a a' z z' = (∏ j, if z j (a', j) = z' j (a, j) then 1 else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2,
        Eight.A lam (ι ((a, a'), k)) (z k.1 (a', k.2)) (z k.2 (a', k.1)) (z' k.1 (a, k.2)) (z' k.2 (a, k.1)) := by sorry

alias «Eight».«rowNetwork_Ψ» := P2M_Eight_rowNetwork___891e43b2654c
