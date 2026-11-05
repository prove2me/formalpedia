-- Prove2me | Theorems.Thm_QueryMachines_Tower_sol_sim
-- name    : QueryMachines.Tower.sol_sim
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:49:48.218605+00:00
-- url     : https://prove2.me/theorems/d085c6a2-75be-4fe4-bf23-f01c2fa5c3db
-- title:
--   Tower: sol sim
-- statement:
--   A run of the solver on the instance at the end of a chain is a run of `nest Sol Inn` with the
--   list env beside every state, at the prices of `Chain.lean`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/TowerRuns.lean#L34-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/TowerRuns.lean#L34-L61

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

theorem QueryMachines.Tower.sol_sim (hM : P.Meets gl wg Sol Inn TS TI SS SI SC) (hG : P.Good c0 f0) (env : List Ctx) (hC : Chain P c0 f0 env) {b : A} {s : Sol.σ} {own : ℕ} {L : List (Ctx ⊕ (Q ⊕ G))}
    (hr : Sol.Reaches (P.oracle gl (parent c0 env) (tabs P f0 env)) SS b s own L) :
    (nest Sol Inn).WithinFrom (callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) (Sum.inl (env, parent c0 env))) (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2) (Sum.inl (env, s) : NSt Sol Inn)
      (own + (L.map (Sum.elim (fun _ => callCost TS TI (P.lev (parent c0 env)) (price P TI tq env)) (Sum.elim (fun _ => price P TI tq env) wg))).sum) (P.lev c0 * (SC + 1) + SS + SI + 2) b := by sorry
