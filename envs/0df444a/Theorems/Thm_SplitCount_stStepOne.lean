-- Prove2me | Theorems.Thm_SplitCount_stStepOne
-- name    : SplitCount.stStepOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:50:53.905212+00:00
-- url     : https://prove2.me/theorems/a08b5c6a-e4ac-4025-ac5e-3d56534afc59
-- title:
--   Split Count: st Step One
-- statement:
--   **Step 1 for COUNT of Algorithm 1.** For 0 < δ' ≤ 1 and every level ℓ with K_ℓ ≥ 72/δ' and e_ℓ ≤
--   δ'/12, `countThree ℓ` does what step 1 says.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/StepOne.lean#L102-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/StepOne.lean#L102-L106

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_Occ_Main
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_Alg
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_StepOne
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ

theorem SplitCount.stStepOne : StStepOne := by sorry
