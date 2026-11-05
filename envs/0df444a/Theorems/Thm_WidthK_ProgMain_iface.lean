-- Prove2me | Theorems.Thm_WidthK_ProgMain_iface
-- name    : WidthK.ProgMain.iface
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:36:37.798572+00:00
-- url     : https://prove2.me/theorems/36f89f1f-f0a1-4d1f-91b8-8a475dfb5ea1
-- title:
--   Prog Main: iface
-- statement:
--   The facts on finite sets that `sparsify_prog_of` needs, for the thresholds `theta τ`, collected
--   from the interface statements.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L208-L233
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L208-L233

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

theorem WidthK.ProgMain.iface (h1 : StNodeRoot) (h2 : StNodeStep) (h3 : StNodeBound) (h4 : StLeafCard) (h5 : StLightEq) (h6 : StHeavyEq) (h7 : StSatIff)
    (h8 : StThr) (h9 : StBetaSum) {τ : ℕ} (hτ : 1 ≤ τ) (k n : ℕ) :
    Iface (theta τ) k (bsum τ k * n) (k * n) τ (leafC τ k * n) (Ok k n)
      (fun F₀ F p t => Ok k n F₀ ∧ Node (theta τ) k τ F₀ F p t) := by sorry
