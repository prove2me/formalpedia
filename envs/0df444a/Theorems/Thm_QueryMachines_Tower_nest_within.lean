-- Prove2me | Theorems.Thm_QueryMachines_Tower_nest_within
-- name    : QueryMachines.Tower.nest_within
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:49:44.108197+00:00
-- url     : https://prove2.me/theorems/f40f5ee9-6646-47a2-9ec9-a4beffb9bb18
-- title:
--   Tower: nest within
-- statement:
--   `nest Sol Inn` meets the hypothesis of `SelfCallRuns`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/TowerRuns.lean#L83-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/TowerRuns.lean#L83-L96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Chain
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_Runs
import Definitions.Def_Tower_TowerRuns
import Theorems.Thm_Groundwork_PolyT_elim

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Ctx Q G A : Type} [HasSize Ctx] {P : Spec Ctx Q A} {gl : G → Option A} {wg : G → ℕ} {Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A} {Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A}
  {TS : ℕ → ℕ → ℕ → ℕ} {TI : ℕ → ℕ → ℕ} {SS SI SC : ℕ} {c0 : Ctx} {f0 : Q → Option A} {tq : ℕ}

theorem QueryMachines.Tower.nest_within (hM : P.Meets gl wg Sol Inn TS TI SS SI SC) (hG : P.Good c0 f0) (x : NIn Ctx Q) (hx : nGood P c0 f0 x) :
    (nest Sol Inn).Within (callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) x) (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2) x (nT P TS TI tq x) (P.lev c0 * (SC + 1) + SS + SI + 2) (nval P c0 f0 x) := by sorry
