-- Prove2me | Theorems.Thm_P2M_Groundwork_Prog_Count_wordNet___eq_78331b67b704
-- name    : P2M_Groundwork_Prog_Count_wordNet___eq_78331b67b704
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:26.158848+00:00
-- url     : https://prove2.me/theorems/3463916a-ea77-48ed-9fa1-672750d095c0
-- title:
--   P2 M Groundwork Prog Count word Net   eq 78331b67b704: P2 M Groundwork Prog Count word Net   eq 78331b67b704
-- statement:
--   The P2 M Groundwork Prog Count word Net   eq 78331b67b704 construction uses the P2 M Groundwork Prog Count word Net   eq 78331b67b704 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L319-L324
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L319-L324

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

theorem P2M_Groundwork_Prog_Count_wordNet___eq_78331b67b704 (hg : 0 < g) (hm : φ.length ≤ g * mu g φ) {a b : Fin g} (h : a < b) (z z' : List Bool) :
    (wordNet g k φ).Ψ a b z z' = (net φ g (mu g φ) k).Ψ a b (bits z) (bits z') := by sorry

alias «Groundwork».«Prog».«Count».«wordNet_Ψ_eq» := P2M_Groundwork_Prog_Count_wordNet___eq_78331b67b704
