-- Prove2me | Theorems.Thm_WidthK_Refine_tryP_none
-- name    : WidthK.Refine.tryP_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:30:55.128907+00:00
-- url     : https://prove2.me/theorems/e7b28276-b5f3-405a-bf9a-04afeab273ee
-- title:
--   Refine: try P none
-- statement:
--   Where `tryP` has no answer at (j, h), no set of size h is a heart for the clauses of size j. The
--   threshold is at least 1, so a
--   heart lies inside some clause and is among the candidates.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L259-L280
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L259-L280

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem WidthK.Refine.tryP_none {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {jh : ℕ × ℕ} (hθ : ∀ r, 1 ≤ r → 1 ≤ θ r) (hs : NF s)
    (hjh : jh ∈ pairsK k) (h : tryP θ k s jh = none) :
    ∀ H : Finset PLit, H.card = jh.2 → ¬ Heart θ (toFin s) jh.1 H := by sorry
