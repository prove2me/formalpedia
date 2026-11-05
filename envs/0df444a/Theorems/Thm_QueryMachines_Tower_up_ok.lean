-- Prove2me | Theorems.Thm_QueryMachines_Tower_up_ok
-- name    : QueryMachines.Tower.up_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:32:21.722757+00:00
-- url     : https://prove2.me/theorems/fc769979-ed07-44e6-a5d6-defd53c6a977
-- title:
--   Tower: up ok
-- statement:
--   A query y that runs up through env, asked by the activation x: it has the answer that `tabs env`
--   or gl gives, at the price `price env` or wg.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Chain.lean#L101-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Chain.lean#L101-L118

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Definitions.Def_Tower_Chain
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Ctx Q G A : Type} (P : Spec Ctx Q A) (TS : ℕ → ℕ → ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (c0 : Ctx) (f0 : Q → Option A) (tq : ℕ)
variable {P TS TI c0 f0} [HasSize Ctx] {gl : G → Option A} {wg : G → ℕ} {Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A} {Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A} {SS SI SC : ℕ}
omit [HasSize Ctx]

theorem QueryMachines.Tower.up_ok (gl : G → Option A) (wg : G → ℕ) (TS : ℕ → ℕ → ℕ → ℕ) (env : List Ctx) (hC : Chain P c0 f0 env) (y : Q ⊕ G) (v : A) (hy : Sum.elim (tabs P f0 env) gl y = some v) (x : NIn Ctx Q)
    (hx : env.length ≤ ndep P x) :
    ∃ r : A ⊕ A, callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) x (upQuery env y) = some r ∧ r.elim id id = v ∧
      (Sum.elim (Sum.elim (fun _ => tq) wg) fun a' => nT P TS TI tq a' + 2) (upQuery env y) = Sum.elim (fun _ => price P TI tq env) wg y := by sorry
