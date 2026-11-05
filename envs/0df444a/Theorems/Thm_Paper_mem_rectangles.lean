-- Prove2me | Theorems.Thm_Paper_mem_rectangles
-- name    : Paper.mem_rectangles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:08:25.696954+00:00
-- url     : https://prove2.me/theorems/41e8cfb4-262b-43ab-bed5-8c0a9b58343a
-- title:
--   Paper: mem rectangles
-- statement:
--   The Paper construction uses the mem rectangles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecLevel_Grid.lean#L48-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecLevel_Grid.lean#L48-L49

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

theorem Paper.mem_rectangles (q : Rectangle g) : q ∈ rectangles g ↔ q.1.1 < q.1.2 ∧ q.2.1 < q.2.2 := by sorry
