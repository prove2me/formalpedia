-- Prove2me | Theorems.Thm_QueryMachines_Tower_costMono
-- name    : QueryMachines.Tower.costMono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:46:16.133528+00:00
-- url     : https://prove2.me/theorems/07cbae5b-9f30-4bac-a718-9f9e69cf2b89
-- title:
--   Tower: cost Mono
-- statement:
--   Dearer queries make the tower dearer, if they make the solver and the procedure dearer.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Cost.lean#L23-L26
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Cost.lean#L23-L26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Mathlib.Tactic.Ring
import Definitions.Def_Tower_Cost
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower

theorem QueryMachines.Tower.costMono {TS : ℕ → ℕ → ℕ → ℕ} {TI : ℕ → ℕ → ℕ} (hS : ∀ l tc tc' tq tq', tc ≤ tc' → tq ≤ tq' → TS l tc tq ≤ TS l tc' tq') (hI : ∀ l t t', t ≤ t' → TI l t ≤ TI l t') :
    ∀ l t t', t ≤ t' → cost TS TI l t ≤ cost TS TI l t'
  := by sorry
