-- Prove2me | Theorems.Thm_QueryMachines_Tower_selfCall_from
-- name    : QueryMachines.Tower.selfCall_from
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:49:11.775182+00:00
-- url     : https://prove2.me/theorems/a1e7e01e-67ad-47ce-b51b-34e27f57e3fc
-- title:
--   Tower: self Call from
-- statement:
--   A run of M from any state, on any stack of waiting activations and with any continuation (see
--   the head of this file).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L66-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L66-L104

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_Runs
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
variable {Q A α β : Type} (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β)

theorem QueryMachines.Tower.selfCall_from (O : Q → Option A) (w : Q → ℕ) (Good : α → Prop) (val : α → β) (dep T : α → ℕ) (S : ℕ)
    (H : ∀ a, Good a → M.Within (callOracle O Good val dep a) (Sum.elim w fun a' => T a' + 2) a (T a) S (val a)) :
    ∀ (n : ℕ) (a : α), dep a = n → Good a → ∀ (s : M.σ) (own : ℕ) (L : List (Q ⊕ α)), M.Reaches (callOracle O Good val dep a) S (val a) s own L →
    ∀ (K : List M.σ) (S' tk : ℕ) (b : β), size K + (dep a + 1) * (S + 1) ≤ S' →
      (∀ sh : M.σ, M.out sh = some (val a) → size sh ≤ S → (selfCall M).WithinFrom O w (sh :: K : List M.σ) tk S' b) →
      (selfCall M).WithinFrom O w (s :: K : List M.σ) (own + (L.map (Sum.elim w fun a' => T a' + 2)).sum + tk) S' b := by sorry
