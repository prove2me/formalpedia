-- Prove2me | Theorems.Thm_SparsificationLemma_Shrink_length_step_le
-- name    : SparsificationLemma.Shrink.length_step_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:07:49.980997+00:00
-- url     : https://prove2.me/theorems/f3255e61-eaa1-4b69-a9cd-bfb67b85c4ad
-- title:
--   Shrink: length step le
-- statement:
--   On lists: for thresholds at least 1, if x.1 is in normal form and none of its clauses contains
--   another, the formulas of both children of x have at most as many clauses as x.1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Shrink.lean#L65-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Shrink.lean#L65-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsificationLemma_Shrink
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog WidthK.ProgMain CountKSat
open SparsificationLemma.Shrink
variable {α : Type} [DecidableEq α] {θ : ℕ → ℕ} {F : Finset (Finset α)} {j : ℕ} {H : Finset α}

theorem SparsificationLemma.Shrink.length_step_le {k : ℕ} (hθ : ∀ i, 1 ≤ θ i) {x l h : CNode} (hx : NF x.1) (hred : Reduced (toFin x.1)) (hst : stepC θ k x = some (l, h)) :
    l.1.length ≤ x.1.length ∧ h.1.length ≤ x.1.length := by sorry
