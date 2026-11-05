-- Prove2me | Theorems.Thm_Paper_card_rectangles_le
-- name    : Paper.card_rectangles_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:08:33.574885+00:00
-- url     : https://prove2.me/theorems/a5c9ab32-0254-41f1-8655-989464f8191c
-- title:
--   Paper: card rectangles le
-- statement:
--   The inequality of the same sentence: |ℛ| ≤ g⁴/4. Same as in the paper.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecLevel_Grid.lean#L57-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecLevel_Grid.lean#L57-L60

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

theorem Paper.card_rectangles_le (g : ℕ) : (#(rectangles g) : ℝ) ≤ (g : ℝ) ^ 4 / 4 := by sorry
