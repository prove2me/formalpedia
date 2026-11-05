-- Prove2me | Theorems.Thm_WidthK_ProgMain_step_spec
-- name    : WidthK.ProgMain.step_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:43:27.956372+00:00
-- url     : https://prove2.me/theorems/19877b71-f5dc-4308-bf2e-7605ff8554c1
-- title:
--   Prog Main: step spec
-- statement:
--   One step of the program is one step of the rule: the two lists it returns are in normal form,
--   and as sets they are the light and the heavy child.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L105-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L105-L114

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_ProgMain
set_option autoImplicit false
section
section
open WidthK WidthK.ProgMain
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}

theorem WidthK.ProgMain.step_spec (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {ψ s l h : PFml} {p t : ℕ} (hG : G Node ψ s p t)
    (hst : stepK θ k s = some (l, h)) :
    ∃ j H, Rule θ k (toFin s) j H ∧ toFin l = light (toFin s) H ∧ toFin h = heavy (toFin s) j H ∧ NF l ∧ NF h := by sorry
