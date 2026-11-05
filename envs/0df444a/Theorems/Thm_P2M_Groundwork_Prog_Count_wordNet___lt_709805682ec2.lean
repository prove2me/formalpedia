-- Prove2me | Theorems.Thm_P2M_Groundwork_Prog_Count_wordNet___lt_709805682ec2
-- name    : P2M_Groundwork_Prog_Count_wordNet___lt_709805682ec2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:43:48.55709+00:00
-- url     : https://prove2.me/theorems/6daa8c7f-53aa-4c65-9a84-1d398b49441f
-- title:
--   P2 M Groundwork Prog Count word Net   lt 709805682ec2: P2 M Groundwork Prog Count word Net   lt 709805682ec2
-- statement:
--   The interaction of clusters a < b on words.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L311-L317
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L311-L317

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}

theorem P2M_Groundwork_Prog_Count_wordNet___lt_709805682ec2 {a b : Fin g} (h : a < b) (z z' : List Bool) : (wordNet g k φ).Ψ a b z z' =
    if ((links g k φ a.val b.val).all fun p => z.getD p.1 false == z'.getD p.2 false) then 1 else 0 := by sorry

alias «Groundwork».«Prog».«Count».«wordNet_Ψ_lt» := P2M_Groundwork_Prog_Count_wordNet___lt_709805682ec2
