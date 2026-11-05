-- Prove2me | Theorems.Thm_QueryMachines_Tower_inn_sim
-- name    : QueryMachines.Tower.inn_sim
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:49:50.997548+00:00
-- url     : https://prove2.me/theorems/153212e6-d71b-4d81-9200-6c5ff50f9fde
-- title:
--   Tower: inn sim
-- statement:
--   The same for a run of the procedure.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/TowerRuns.lean#L64-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/TowerRuns.lean#L64-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Chain
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_Runs
import Definitions.Def_Tower_TowerRuns
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Ctx Q G A : Type} [HasSize Ctx] {P : Spec Ctx Q A} {gl : G → Option A} {wg : G → ℕ} {Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A} {Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A}
  {TS : ℕ → ℕ → ℕ → ℕ} {TI : ℕ → ℕ → ℕ} {SS SI SC : ℕ} {c0 : Ctx} {f0 : Q → Option A} {tq : ℕ}

theorem QueryMachines.Tower.inn_sim (hM : P.Meets gl wg Sol Inn TS TI SS SI SC) (hG : P.Good c0 f0) (env : List Ctx) (hC : Chain P c0 f0 env) (c : Ctx) (q : Q) {b : A} {i : Inn.σ} {own : ℕ} {L : List (Q ⊕ G)}
    (hr : Inn.Reaches (Sum.elim (tabs P f0 env) gl) SI b i own L) :
    (nest Sol Inn).WithinFrom (callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) (Sum.inr (c, env, q))) (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2) (Sum.inr (env, i) : NSt Sol Inn) (own + (L.map (Sum.elim (fun _ => price P TI tq env) wg)).sum) (P.lev c0 * (SC + 1) + SS + SI + 2) b := by sorry
