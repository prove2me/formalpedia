-- Prove2me | Theorems.Thm_P2M_Groundwork_Network___pull_e5947ed64801
-- name    : P2M_Groundwork_Network___pull_e5947ed64801
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:33:59.834412+00:00
-- url     : https://prove2.me/theorems/2c92b0e6-0717-4348-92c9-10ad07226d7d
-- title:
--   P2 M Groundwork Network   pull e5947ed64801: P2 M Groundwork Network   pull e5947ed64801
-- statement:
--   The P2 M Groundwork Network   pull e5947ed64801 construction uses the P2 M Groundwork Network   pull e5947ed64801 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Pull.lean#L41-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Pull.lean#L41-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Definitions.Def_StepMachines_Math_Pull
set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Network
variable {J σ τ : Type*}
variable [Fintype J] [LinearOrder J] (N : Network J σ τ) (n : J → ℕ) (cs : ∀ a, Code (N.S a) (n a))
  (cl : ∀ a b, Code (N.Θ a b) (N.c a b))
omit [Fintype J]

theorem P2M_Groundwork_Network___pull_e5947ed64801 (a b : J) (z z' : List Bool) :
    (N.pull n cs cl).Ψ a b z z' = N.Ψ a b ((cs a).dec z) ((cs b).dec z') := by sorry

alias «Groundwork».«Network».«Ψ_pull» := P2M_Groundwork_Network___pull_e5947ed64801
