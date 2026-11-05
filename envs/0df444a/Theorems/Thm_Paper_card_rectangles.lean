-- Prove2me | Theorems.Thm_Paper_card_rectangles
-- name    : Paper.card_rectangles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:08:50.767951+00:00
-- url     : https://prove2.me/theorems/41c5a14d-6b04-4696-a07a-b51b1c0f1efa
-- title:
--   Paper: card rectangles
-- statement:
--   The number of rectangles. The paper: «The set ℛ of rectangles has C(g,2)² ≤ g⁴/4 elements.» This
--   is the equality. Same as in the paper.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecLevel_Grid.lean#L53-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecLevel_Grid.lean#L53-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_DefFactor
import Definitions.Def_Paper_SecCrossing_Crossing
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Paper_SecLevel_Grid
set_option autoImplicit false
section
section
open Paper
open Finset Groundwork
variable {g lam : ℕ}

theorem Paper.card_rectangles (g : ℕ) : #(rectangles g) = g.choose 2 ^ 2 := by sorry
