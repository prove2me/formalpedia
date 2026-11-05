-- Prove2me | Theorems.Thm_WidthK_ProgMain_G_step
-- name    : WidthK.ProgMain.G_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:37:22.648946+00:00
-- url     : https://prove2.me/theorems/1c5def42-7d0b-49db-bb0d-c8a675909043
-- title:
--   Prog Main: G step
-- statement:
--   Both children of a step satisfy the invariant: one more step, and q more units at the heavy
--   child.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L118-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L118-L122

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

theorem WidthK.ProgMain.G_step (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) (ψ : PFml) (s : PFml) (p t : ℕ) (l h : PFml)
    (hG : G Node ψ s p t) (hst : stepK θ k s = some (l, h)) : G Node ψ l (p + 1) t ∧ G Node ψ h (p + 1) (t + q) := by sorry
