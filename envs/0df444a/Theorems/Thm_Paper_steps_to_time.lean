-- Prove2me | Theorems.Thm_Paper_steps_to_time
-- name    : Paper.steps_to_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:49:06.297319+00:00
-- url     : https://prove2.me/theorems/7e8d3d2f-5817-4a36-849e-e8c23878b40d
-- title:
--   Paper: steps to time
-- statement:
--   **From steps to time.** A step machine with polynomial-time steps that decides 3-SAT within c ·
--   2^{(δ/2)n} steps, on states of
--   polynomial size, gives a Turing machine that decides 3-SAT in time O(2^{δn}). (No counterpart in the
--   paper, which counts
--   operations informally.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecNetworks_Model.lean#L67-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecNetworks_Model.lean#L67-L74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmEveryDeltaStatement
import Definitions.Def_StepMachineStatements
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_Paper_SecNetworks_Model
set_option autoImplicit false
section
section
open Paper
open Groundwork

theorem Paper.steps_to_time {δ : ℝ} (hδ : 0 < δ) (M : StepMachine (List Bool) Bool) (hM : PolyTimeSteps M)
    (h : DecidesInSteps M (δ / 2)) : Sat3.DecidedInTime δ := by sorry
