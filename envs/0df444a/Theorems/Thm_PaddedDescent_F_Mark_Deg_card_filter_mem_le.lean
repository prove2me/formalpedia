-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Deg_card_filter_mem_le
-- name    : PaddedDescent.F.Mark.Deg.card_filter_mem_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:26:21.998135+00:00
-- url     : https://prove2.me/theorems/08c0aa6b-0acd-4546-bbe6-ab44d6095ab2
-- title:
--   Deg: card filter mem le
-- statement:
--   At a leaf whose clauses have 1 to k literals, a literal lies in at most θ 0 + … + θ (k − 1)
--   clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L55-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L55-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_PaddedDescent_F_MarkDeg
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Deg
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify
open WidthK (theta bsum leafC lay)
open WidthK.Prog (stepK NF toFin)
variable {α : Type*} [DecidableEq α] {θ : ℕ → ℕ} {k : ℕ} {F : Finset (Finset α)}

theorem PaddedDescent.F.Mark.Deg.card_filter_mem_le (hθ : ∀ i, 0 < θ i) (h : WidthK.Leaf θ k F) (hF : ∀ C ∈ F, 1 ≤ C.card ∧ C.card ≤ k) (y : α) :
    (F.filter fun C => y ∈ C).card ≤ ∑ i ∈ range k, θ i := by sorry
