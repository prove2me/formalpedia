-- Prove2me | Theorems.Thm_WidthK_ProgMain_sparsify_prog_of
-- name    : WidthK.ProgMain.sparsify_prog_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:43:37.503226+00:00
-- url     : https://prove2.me/theorems/14ef7e22-feb7-4fa2-bcb6-6b0f00d7030e
-- title:
--   Prog Main: sparsify prog of
-- statement:
--   The sparsification lemma for the program `stepK`, for any thresholds θ and any bounds D, T, q,
--   leafB for which the facts on finite sets (`Iface`) and
--   the refinement (`Refines`) hold. hv bounds the number of heavy steps on a path.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L139-L190
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L139-L190

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_ProgMain
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open WidthK WidthK.ProgMain
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}

theorem WidthK.ProgMain.sparsify_prog_of (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {n hv : ℕ} (hT : T < (hv + 1) * q) (ψ : PFml)
    (hOk : Ok (toFin ψ)) (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    let L := leaves (stepK θ k) D (rootP ψ)
    L.length ≤ ∑ j ∈ range (hv + 1), D.choose j ∧
    (∀ x ∈ L, stepK θ k x = none ∧ x.length ≤ leafB ∧ ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧
    (∀ v : PLit → Prop, (∀ C ∈ ψ, ∃ a ∈ C, v a) ↔ ∃ x ∈ L, ∀ C ∈ x, ∃ a ∈ C, v a) ∧
    ∀ i, ((round (stepK θ k))^[i] ([rootP ψ], [])).1.length ≤ D + 1 ∧
      ∀ x ∈ ((round (stepK θ k))^[i] ([rootP ψ], [])).1, x.length ≤ ψ.length * 2 ^ k ∧
        ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by sorry
