-- Prove2me | Theorems.Thm_QueryMachines_Tower_chain_facts
-- name    : QueryMachines.Tower.chain_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:26:41.778436+00:00
-- url     : https://prove2.me/theorems/2d7bcbda-1e39-43fc-ac5f-1693cafea269
-- title:
--   Tower: chain facts
-- statement:
--   Along a chain: the instance is well formed, the depths add up, the list is small.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Chain.lean#L84-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Chain.lean#L84-L96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Definitions.Def_Tower_Chain
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Ctx Q G A : Type} (P : Spec Ctx Q A) (TS : ℕ → ℕ → ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (c0 : Ctx) (f0 : Q → Option A) (tq : ℕ)
variable {P TS TI c0 f0} [HasSize Ctx] {gl : G → Option A} {wg : G → ℕ} {Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A} {Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A} {SS SI SC : ℕ}

theorem QueryMachines.Tower.chain_facts (hM : P.Meets gl wg Sol Inn TS TI SS SI SC) (hG : P.Good c0 f0) : ∀ env : List Ctx, Chain P c0 f0 env →
    P.Good (parent c0 env) (tabs P f0 env) ∧ P.lev (parent c0 env) + env.length = P.lev c0 ∧ size env ≤ env.length * (SC + 1) + 1
  := by sorry
