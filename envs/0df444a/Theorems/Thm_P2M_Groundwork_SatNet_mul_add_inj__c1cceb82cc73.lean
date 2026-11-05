-- Prove2me | Theorems.Thm_P2M_Groundwork_SatNet_mul_add_inj__c1cceb82cc73
-- name    : P2M_Groundwork_SatNet_mul_add_inj__c1cceb82cc73
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:57:32.963772+00:00
-- url     : https://prove2.me/theorems/d1e7f9d3-c228-4210-808f-ce9fe9a1cc10
-- title:
--   P2 M Groundwork Sat Net mul add inj  c1cceb82cc73: P2 M Groundwork Sat Net mul add inj  c1cceb82cc73
-- statement:
--   The P2 M Groundwork Sat Net mul add inj  c1cceb82cc73 construction uses the P2 M Groundwork Sat Net mul add inj  c1cceb82cc73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L109-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L109-L110

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_StepMachines_Math_SatNet
set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}

theorem P2M_Groundwork_SatNet_mul_add_inj__c1cceb82cc73 {k x y j j' : ℕ} (hj : j < k) (hj' : j' < k) (h : x * k + j = y * k + j') :
    x = y ∧ j = j' := by sorry

alias «Groundwork».«SatNet».«mul_add_inj'» := P2M_Groundwork_SatNet_mul_add_inj__c1cceb82cc73
